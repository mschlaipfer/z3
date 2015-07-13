/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_instruction.cpp

Abstract:

    <abstract>

Author:

    Krystof Hoder (t-khoder) 2010-09-14.

Revision History:

--*/

#include"ast_pp.h"
#include"stopwatch.h"
#include"dl_context.h"
#include"dl_util.h"
#include"dl_instruction.h"
#include"rel_context.h"
#include"debug.h"
#include"warning.h"
#include"dl_compiler.h"

namespace datalog {

    // -----------------------------------
    //
    // execution_context
    //
    // -----------------------------------
    
    execution_context::execution_context(context & context) 
        : m_context(context),
        m_stopwatch(0),
        m_timelimit_ms(0) {}

    execution_context::~execution_context() {
        reset();
        dealloc(m_stopwatch);
    }

    void execution_context::reset() {
        reg_vector::iterator it=m_registers.begin();
        reg_vector::iterator end=m_registers.end();
        for(; it != end; ++it) {
            relation_base * rel = *it;
            if (rel) {
                rel->deallocate();
            }
        }
        m_registers.reset();
        m_reg_annotation.reset();
        reset_timelimit();
    }

    rel_context& execution_context::get_rel_context() { 
        return dynamic_cast<rel_context&>(*m_context.get_rel_context()); 
    }

    rel_context const& execution_context::get_rel_context() const { 
        return dynamic_cast<rel_context const&>(*m_context.get_rel_context()); 
    }

    struct compare_size_proc {
        typedef std::pair<unsigned, unsigned> pr;
        bool operator()(pr const& a, pr const& b) const {
            return a.second > b.second;
        }
    };

    void execution_context::report_big_relations(unsigned threshold, std::ostream & out) const {
        unsigned n = register_count();
        svector<std::pair<unsigned, unsigned> > sizes;
        size_t total_bytes = 0;
        for(unsigned i = 0; i < n; i++) {
            unsigned sz = reg(i) ? reg(i)->get_size_estimate_bytes() : 0;
            total_bytes += sz;
            sizes.push_back(std::make_pair(i, sz));
        }
        std::sort(sizes.begin(), sizes.end(), compare_size_proc());        

        out << "bytes " << total_bytes << "\n";
        out << "bytes\trows\tannotation\n";
        for(unsigned i = 0; i < n; i++) {
            unsigned sz = sizes[i].second;
            unsigned rg = sizes[i].first;
            unsigned rows = reg(rg) ? reg(rg)->get_size_estimate_rows() : 0;
            if (sz < threshold) {
                continue;
            }
            std::string annotation;
            get_register_annotation(i, annotation);
            out << sz << "\t" << rows << "\t" << annotation << "\n";
        }
    }

    void execution_context::set_timelimit(unsigned time_in_ms) {
        SASSERT(time_in_ms > 0);
        m_timelimit_ms = time_in_ms;
        if (!m_stopwatch) {
            m_stopwatch = alloc(stopwatch);
        }
        m_stopwatch->stop();
        m_stopwatch->reset();
        m_stopwatch->start();
    }
    void execution_context::reset_timelimit() {
        if (m_stopwatch) {
            m_stopwatch->stop();
        }
        m_timelimit_ms = 0;
    }

    bool execution_context::should_terminate() {
        return 
            m_context.canceled() ||
            memory::above_high_watermark() ||
            (m_stopwatch && 
             m_timelimit_ms != 0 &&
             m_timelimit_ms < static_cast<unsigned>(1000*m_stopwatch->get_current_seconds()));
    }

    void execution_context::collect_statistics(statistics& st) const {
        st.update("dl.joins",   m_stats.m_join);
        st.update("dl.project", m_stats.m_project);
        st.update("dl.filter",  m_stats.m_filter);
        st.update("dl.total", m_stats.m_total);
        st.update("dl.unary_singleton", m_stats.m_unary_singleton);
        st.update("dl.filter_by_negation", m_stats.m_filter_by_negation);
        st.update("dl.select_equal_project", m_stats.m_select_equal_project);
        st.update("dl.join_project", m_stats.m_join_project);
        st.update("dl.project_rename", m_stats.m_project_rename);
        st.update("dl.union", m_stats.m_union);
        st.update("dl.filter_interpreted_project", m_stats.m_filter_interp_project);
        st.update("dl.filter_id", m_stats.m_filter_id);
        st.update("dl.filter_eq", m_stats.m_filter_eq);
    }


    // -----------------------------------
    //
    // instruction
    //
    // -----------------------------------

    instruction::~instruction() {
        fn_cache::iterator it = m_fn_cache.begin();
        fn_cache::iterator end = m_fn_cache.end();
        for(; it != end; ++it) {
            dealloc(it->m_value);
        }
    }

    void instruction::process_all_costs() {
        process_costs();
    }

    void instruction::collect_statistics(statistics& st) const {
        costs c;
        get_total_cost(c);
        st.update("instruction", c.instructions);
        st.update("instruction-time", c.milliseconds);
    }


    void instruction::display_indented(execution_context const & _ctx, std::ostream & out, std::string indentation) const {
        out << indentation;
        rel_context const& ctx = _ctx.get_rel_context();
        display_head_impl(_ctx, out);
        if (ctx.output_profile()) {
            out << " {";
            output_profile(out);
            out << '}';
        }
        out << "\n";
        display_body_impl(_ctx, out, indentation);
    }

    void instruction::log_verbose(execution_context& ctx) {
        IF_VERBOSE(2, display(ctx, verbose_stream()););
    }

    class instr_io : public instruction {
        bool m_store;
        func_decl_ref m_pred;
        reg_idx m_reg;
    public:
        instr_io(bool store, func_decl_ref pred, reg_idx reg)
            : m_store(store), m_pred(pred), m_reg(reg) {}
        virtual bool perform(execution_context & ctx) {
            log_verbose(ctx);            
            if (m_store) {
                if (ctx.reg(m_reg)) {
                    ctx.get_rel_context().store_relation(m_pred, ctx.release_reg(m_reg));
                }
                else {
                    rel_context & dctx = ctx.get_rel_context();
                    relation_base * empty_rel;
                    //the object referenced by sig is valid only until we call dctx.store_relation()
                    const relation_signature & sig = dctx.get_relation(m_pred).get_signature();
                    empty_rel = dctx.get_rmanager().mk_empty_relation(sig, m_pred.get());
                    dctx.store_relation(m_pred, empty_rel);
                }
            }
            else {
                relation_base& rel = ctx.get_rel_context().get_relation(m_pred);
                if (!rel.fast_empty()) {
                    ctx.set_reg(m_reg, rel.clone());
                }
                else {
                    ctx.make_empty(m_reg);
                }
            }
            return true;
        }
        virtual void make_annotations(execution_context & ctx) {
            ctx.set_register_annotation(m_reg, m_pred->get_name().bare_str());
        }
        virtual void display_head_impl(execution_context const& ctx, std::ostream & out) const {
            const char * rel_name = m_pred->get_name().bare_str();
            if (m_store) {
                out << "store " << m_reg << " into " << rel_name;
            }
            else {
                out << "load " << rel_name << " into " << m_reg;
            }
        }
    };

    instruction * instruction::mk_load(ast_manager & m, func_decl * pred, reg_idx tgt) {
        return alloc(instr_io, false, func_decl_ref(pred, m), tgt);
    }

    instruction * instruction::mk_store(ast_manager & m, func_decl * pred, reg_idx src) {
        return alloc(instr_io, true, func_decl_ref(pred, m), src);
    }


    class instr_dealloc : public instruction {
        reg_idx m_reg;
    public:
        instr_dealloc(reg_idx reg) : m_reg(reg) {}
        virtual bool perform(execution_context & ctx) {
            log_verbose(ctx);
            ctx.make_empty(m_reg);
            return true;
        }
        virtual void make_annotations(execution_context & ctx) {
            ctx.set_register_annotation(m_reg, "alloc");
        }
        virtual void display_head_impl(execution_context const& ctx, std::ostream & out) const {
            out << "dealloc " << m_reg;
        }
    };

    instruction * instruction::mk_dealloc(reg_idx reg) {
        return alloc(instr_dealloc, reg);
    }

    class instr_clone_move : public instruction {
        bool m_clone;
        reg_idx m_src;
        reg_idx m_tgt;
    public:
        instr_clone_move(bool clone, reg_idx src, reg_idx tgt)
            : m_clone(clone), m_src(src), m_tgt(tgt) {}
        virtual bool perform(execution_context & ctx) {
            log_verbose(ctx);            
            if (m_clone) {
                ctx.set_reg(m_tgt, ctx.reg(m_src) ? ctx.reg(m_src)->clone() : 0);
            }
            else {
                ctx.set_reg(m_tgt, ctx.reg(m_src) ? ctx.release_reg(m_src) : 0);
            }
            return true;
        }
        virtual void make_annotations(execution_context & ctx) {
            std::string str;
            if (ctx.get_register_annotation(m_src, str)) {
                ctx.set_register_annotation(m_tgt, str);
            }
            else if (ctx.get_register_annotation(m_tgt, str)) {
                ctx.set_register_annotation(m_src, str);
            }
        }
        virtual void display_head_impl(execution_context const& ctx, std::ostream & out) const {
            out << (m_clone ? "clone " : "move ") << m_src << " into " << m_tgt;
        }
    };

    instruction * instruction::mk_clone(reg_idx from, reg_idx to) {
        return alloc(instr_clone_move, true, from, to);
    }
    instruction * instruction::mk_move(reg_idx from, reg_idx to) {
        return alloc(instr_clone_move, false, from, to);
    }


    class instr_while_loop : public instruction {
        typedef const vector<reg_idx> idx_vector;
        idx_vector m_controls;
        instruction_block * m_body;

        bool control_is_empty(execution_context & ctx) {
            idx_vector::const_iterator it=m_controls.begin();
            idx_vector::const_iterator end=m_controls.end();
            for(; it != end; ++it) {
                reg_idx r = *it;
                if (ctx.reg(r) && !ctx.reg(r)->fast_empty()) {
                    return false;
                }
            }
            return true;
        }
    protected:
        virtual void process_all_costs() {
            instruction::process_all_costs();
            m_body->process_all_costs();
        }
    public:
        instr_while_loop(unsigned control_reg_cnt, const reg_idx * control_regs, instruction_block * body)
            : m_controls(control_reg_cnt, control_regs), m_body(body) {}
        virtual ~instr_while_loop() {
            dealloc(m_body);
        }
        virtual bool perform(execution_context & ctx) {
            log_verbose(ctx);            
            TRACE("dl", tout << "loop entered\n";);
            unsigned count = 0;
            while (!control_is_empty(ctx)) {
                IF_VERBOSE(10, verbose_stream() << "looping ... " << count++ << "\n";);
                if (!m_body->perform(ctx)) {
                    TRACE("dl", tout << "while loop terminated before completion\n";);
                    return false;
                }
            }
            TRACE("dl", tout << "while loop exited\n";);
            return true;
        }
        virtual void make_annotations(execution_context & ctx) {
            m_body->make_annotations(ctx);
        }
        virtual void display_head_impl(execution_context const & ctx, std::ostream & out) const {
            out << "while";
            print_container(m_controls, out);
        }
        virtual void display_body_impl(execution_context const & ctx, std::ostream & out, std::string indentation) const {
            m_body->display_indented(ctx, out, indentation+"    ");
        }
    };

    instruction * instruction::mk_while_loop(unsigned control_reg_cnt, const reg_idx * control_regs, 
            instruction_block * body) {
        return alloc(instr_while_loop, control_reg_cnt, control_regs, body);
    }

    class instr_multiary_join : public instruction {
      typedef unsigned_vector column_vector;
      reg_idx m_result;
      vector<column_vector> m_cols1;
      vector<column_vector> m_cols2;
      svector<reg_idx> m_regs;
    public:
      instr_multiary_join(const reg_idx * tail_regs, unsigned pt_len,
        const vector<variable_intersection> & join_vars, reg_idx result_reg)
        : m_result(result_reg) {
        SASSERT(pt_len > 2);
        SASSERT(pt_len == join_vars.size() + 1);
        // copying stuff
        vector<variable_intersection>::const_iterator it = join_vars.begin(), end = join_vars.end();
        unsigned i = 0;
        m_regs.push_back(tail_regs[i]);
        for (; it != end; ++it) {
          m_cols1.push_back(column_vector(it->size(), it->get_cols1()));
          m_cols2.push_back(column_vector(it->size(), it->get_cols2()));
          m_regs.push_back(tail_regs[i + 1]);
          i++;
        }
      }
      virtual bool perform(execution_context & ctx) {
        log_verbose(ctx);

        // check if any of the regs contains an empty relation
        ++ctx.m_stats.m_multiary_join;
        svector<reg_idx>::const_iterator it = m_regs.begin(), end = m_regs.end(); 
        for (; it != end; ++it) {
          if (!ctx.reg(*it)) {
            ctx.make_empty(m_result);
            return true;
          }
        }

        reg_idx join_reg1 = m_regs[0];
        it = m_regs.begin() + 1, end = m_regs.end();
        unsigned i = 0;
        for (; it != end; ++it) {
          reg_idx join_reg2 = *it;
          const relation_base & r1 = *ctx.reg(join_reg1);
          const relation_base & r2 = *ctx.reg(join_reg2);
          relation_join_fn * fn;
          /* slower with caching
          if (!find_fn(r1, r2, i, fn)) {*/
          fn = r1.get_manager().mk_join_fn(r1, r2, m_cols1[i], m_cols2[i]);
          if (!fn) {
            throw default_exception("trying to perform unsupported join operation on relations of kinds %s and %s",
              r1.get_plugin().get_name().bare_str(), r2.get_plugin().get_name().bare_str());
          }
          /*  store_fn(r1, r2, i, fn);
          }*/

          TRACE("dl",
          r1.get_signature().output(ctx.get_rel_context().get_manager(), tout);
          tout << ":" << r1.get_size_estimate_rows() << " x ";
          r2.get_signature().output(ctx.get_rel_context().get_manager(), tout);
          tout << ":" << r2.get_size_estimate_rows() << " ->\n";);

          ctx.set_reg(m_result, (*fn)(r1, r2));

          TRACE("dl",
            ctx.reg(m_result)->get_signature().output(ctx.get_rel_context().get_manager(), tout);
          tout << ":" << ctx.reg(m_result)->get_size_estimate_rows() << "\n";);

          if (ctx.reg(m_result)->fast_empty()) {
            ctx.make_empty(m_result);
            return true;
          }

          join_reg1 = m_result;
          i++;
        }

        return true;
      }
      virtual void make_annotations(execution_context & ctx) {
        /*
        std::string a1 = "rel1", a2 = "rel2";
        ctx.get_register_annotation(m_rel1, a1);
        ctx.get_register_annotation(m_rel1, a1);
        ctx.set_register_annotation(m_res, "join " + a1 + " " + a2);
        */
      }
      virtual void display_head_impl(execution_context const & ctx, std::ostream & out) const {
        out << "multiary_join " << *m_regs.begin();
        svector<reg_idx>::const_iterator it = m_regs.begin() + 1, end = m_regs.end();
        unsigned i = 0;
        for (; it != end; ++it) {
          out << " ";
          print_container(m_cols1[i], out);
          out << " and ";
          print_container(m_cols2[i], out);
          out << " " << *it;
          i++;
        }
        out << " into " << m_result;
      }
    };

    instruction * instruction::mk_multiary_join(const reg_idx * tail_regs, unsigned pt_len,
      const vector<variable_intersection> & join_vars, reg_idx result_reg) {
      return alloc(instr_multiary_join, tail_regs, pt_len, join_vars, result_reg);
    }


    class instr_join : public instruction {
        typedef unsigned_vector column_vector;
        reg_idx m_rel1;
        reg_idx m_rel2;
        column_vector m_cols1;
        column_vector m_cols2;
        reg_idx m_res;
    public:
        instr_join(reg_idx rel1, reg_idx rel2, unsigned col_cnt, const unsigned * cols1, 
            const unsigned * cols2, reg_idx result)
            : m_rel1(rel1), m_rel2(rel2), m_cols1(col_cnt, cols1), 
            m_cols2(col_cnt, cols2), m_res(result) {}
        virtual bool perform(execution_context & ctx) {
            log_verbose(ctx);            
            ++ctx.m_stats.m_join;
            if (!ctx.reg(m_rel1) || !ctx.reg(m_rel2)) {
                ctx.make_empty(m_res);
                return true;
            }
            relation_join_fn * fn;
            const relation_base & r1 = *ctx.reg(m_rel1);
            const relation_base & r2 = *ctx.reg(m_rel2);
            if (!find_fn(r1, r2, fn)) {
                fn = r1.get_manager().mk_join_fn(r1, r2, m_cols1, m_cols2);
                TRACE("dl", tout << "creating new join " << &fn << "\n";);
                if (!fn) {
                    throw default_exception("trying to perform unsupported join operation on relations of kinds %s and %s",
                        r1.get_plugin().get_name().bare_str(), r2.get_plugin().get_name().bare_str());
                }
                store_fn(r1, r2, fn);
            }

            TRACE("dl",
                r1.get_signature().output(ctx.get_rel_context().get_manager(), tout);
                tout<<":"<<r1.get_size_estimate_rows()<<" x ";
                r2.get_signature().output(ctx.get_rel_context().get_manager(), tout);
                tout<<":"<<r2.get_size_estimate_rows()<<" ->\n";);

            ctx.set_reg(m_res, (*fn)(r1, r2));

            TRACE("dl", 
                ctx.reg(m_res)->get_signature().output(ctx.get_rel_context().get_manager(), tout);
                tout<<":"<<ctx.reg(m_res)->get_size_estimate_rows()<<"\n";);

            if (ctx.reg(m_res)->fast_empty()) {
                ctx.make_empty(m_res);
            }
            return true;
        }
        virtual void make_annotations(execution_context & ctx) {
            std::string a1 = "rel1", a2 = "rel2";
            ctx.get_register_annotation(m_rel1, a1);
            ctx.get_register_annotation(m_rel2, a2);
            ctx.set_register_annotation(m_res, "join " + a1 + " " + a2);
        }
        virtual void display_head_impl(execution_context const & ctx, std::ostream & out) const {
            out << "join " << m_rel1;
            print_container(m_cols1, out);
            out << " and " << m_rel2;
            print_container(m_cols2, out);
            out << " into " << m_res;
        }
    };

    instruction * instruction::mk_join(reg_idx rel1, reg_idx rel2, unsigned col_cnt,
            const unsigned * cols1, const unsigned * cols2, reg_idx result) {
        return alloc(instr_join, rel1, rel2, col_cnt, cols1, cols2, result);
    }

    class instr_filter_equal : public instruction {
        reg_idx m_reg;
        app_ref m_value;
        unsigned m_col;
    public:
        instr_filter_equal(ast_manager & m, reg_idx reg, const relation_element & value, unsigned col)
            : m_reg(reg), m_value(value, m), m_col(col) {}
        virtual bool perform(execution_context & ctx) {
            log_verbose(ctx);            
            ++ctx.m_stats.m_filter_eq;
            if (!ctx.reg(m_reg)) {
                return true;
            }

            relation_mutator_fn * fn;
            relation_base & r = *ctx.reg(m_reg);
            if (!find_fn(r, fn)) {
                fn = r.get_manager().mk_filter_equal_fn(r, m_value, m_col);
                if (!fn) {
                    throw default_exception(
                        "trying to perform unsupported filter_equal operation on a relation of kind %s",
                        r.get_plugin().get_name().bare_str());
                }
                store_fn(r, fn);
            }
            (*fn)(r);

            if (r.fast_empty()) {
                ctx.make_empty(m_reg);
            }
            return true;
        }
        virtual void make_annotations(execution_context & ctx) {
            std::stringstream a;
            a << "filter_equal " << m_col << " val: " << ctx.get_rel_context().get_rmanager().to_nice_string(m_value);
            ctx.set_register_annotation(m_reg, a.str());
        }
        virtual void display_head_impl(execution_context const& ctx, std::ostream & out) const {
            out << "filter_equal " << m_reg << " col: " << m_col << " val: "
                << ctx.get_rel_context().get_rmanager().to_nice_string(m_value);
        }
    };

    instruction * instruction::mk_filter_equal(ast_manager & m, reg_idx reg, const relation_element & value, 
            unsigned col) {
        return alloc(instr_filter_equal, m, reg, value, col);
    }


    class instr_filter_identical : public instruction {
        typedef unsigned_vector column_vector;
        reg_idx m_reg;
        column_vector m_cols;
    public:
        instr_filter_identical(reg_idx reg, unsigned col_cnt, const unsigned * identical_cols)
            : m_reg(reg), m_cols(col_cnt, identical_cols) {}
        virtual bool perform(execution_context & ctx) {
            log_verbose(ctx);            
            ++ctx.m_stats.m_filter_id;
            if (!ctx.reg(m_reg)) {
                return true;
            }

            relation_mutator_fn * fn;
            relation_base & r = *ctx.reg(m_reg);
            if (!find_fn(r, fn)) {
                fn = r.get_manager().mk_filter_identical_fn(r, m_cols.size(), m_cols.c_ptr());
                if (!fn) {
                    throw default_exception(
                        "trying to perform unsupported filter_identical operation on a relation of kind %s",
                        r.get_plugin().get_name().bare_str());
                }
                store_fn(r, fn);
            }
            (*fn)(r);

            if (r.fast_empty()) {
                ctx.make_empty(m_reg);
            }
            return true;
        }
        virtual void display_head_impl(execution_context const& ctx, std::ostream & out) const {
            out << "filter_identical " << m_reg << " ";
            print_container(m_cols, out);
        }
        virtual void make_annotations(execution_context & ctx) {
            ctx.set_register_annotation(m_reg, "filter_identical");
        }
    };

    instruction * instruction::mk_filter_identical(reg_idx reg, unsigned col_cnt, const unsigned * identical_cols) {
        return alloc(instr_filter_identical, reg, col_cnt, identical_cols);
    }


    class instr_filter_interpreted : public instruction {
        reg_idx m_reg;
        app_ref m_cond;
    public:
        instr_filter_interpreted(reg_idx reg, app_ref & condition)
            : m_reg(reg), m_cond(condition) {}
        virtual bool perform(execution_context & ctx) {
            log_verbose(ctx);
            if (!ctx.reg(m_reg)) {
                return true;
            }           
            ++ctx.m_stats.m_filter;

            relation_mutator_fn * fn;
            relation_base & r = *ctx.reg(m_reg);
            TRACE("dl_verbose", r.display(tout <<"pre-filter-interpreted:\n"););
            if (!find_fn(r, fn)) {
                fn = r.get_manager().mk_filter_interpreted_fn(r, m_cond);
                if (!fn) {
                    throw default_exception(
                        "trying to perform unsupported filter_interpreted operation on a relation of kind %s",
                        r.get_plugin().get_name().bare_str());
                }
                store_fn(r, fn);
            }
            (*fn)(r);

            if (r.fast_empty()) {
                ctx.make_empty(m_reg);
            }            
            TRACE("dl_verbose", r.display(tout <<"post-filter-interpreted:\n"););

            return true;
        }
        virtual void display_head_impl(execution_context const& ctx, std::ostream & out) const {
            out << "filter_interpreted " << m_reg << " using "
                << mk_pp(m_cond, m_cond.get_manager());
        }
        virtual void make_annotations(execution_context & ctx) {
            std::stringstream a;
            a << "filter_interpreted " << mk_pp(m_cond, m_cond.get_manager());
            ctx.set_register_annotation(m_reg, a.str());
        }

    };

    instruction * instruction::mk_filter_interpreted(reg_idx reg, app_ref & condition) {
        return alloc(instr_filter_interpreted, reg, condition);
    }

    class instr_filter_interpreted_and_project : public instruction {
        reg_idx m_src;
        app_ref m_cond;
        unsigned_vector m_cols;
        reg_idx m_res;
    public:
        instr_filter_interpreted_and_project(reg_idx src, app_ref & condition,
            unsigned col_cnt, const unsigned * removed_cols, reg_idx result)
            : m_src(src), m_cond(condition), m_cols(col_cnt, removed_cols),
              m_res(result) {}

        virtual bool perform(execution_context & ctx) {
            log_verbose(ctx);
            if (!ctx.reg(m_src)) {
                ctx.make_empty(m_res);
                return true;
            }
            ++ctx.m_stats.m_filter_interp_project;

            relation_transformer_fn * fn;
            relation_base & reg = *ctx.reg(m_src);
            TRACE("dl_verbose", reg.display(tout <<"pre-filter-interpreted-and-project:\n"););
            if (!find_fn(reg, fn)) {
                fn = reg.get_manager().mk_filter_interpreted_and_project_fn(reg, m_cond, m_cols.size(), m_cols.c_ptr());
                if (!fn) {
                    throw default_exception(
                        "trying to perform unsupported filter_interpreted_and_project operation on a relation of kind %s",
                        reg.get_plugin().get_name().bare_str());
                }
                store_fn(reg, fn);
            }

            ctx.set_reg(m_res, (*fn)(reg));


            if (ctx.reg(m_res)->fast_empty()) {
                ctx.make_empty(m_res);
            }
            TRACE("dl_verbose", reg.display(tout << "post-filter-interpreted-and-project:\n"););
            return true;
        }

        virtual void display_head_impl(execution_context const& ctx, std::ostream & out) const {
            out << "filter_interpreted_and_project " << m_src << " into " << m_res;
            out << " using " << mk_pp(m_cond, m_cond.get_manager());
            out << " deleting columns ";
            print_container(m_cols, out);
        }

        virtual void make_annotations(execution_context & ctx) {
            std::stringstream s;
            std::string a = "rel_src";
            ctx.get_register_annotation(m_src, a);
            s << "filter_interpreted_and_project " << mk_pp(m_cond, m_cond.get_manager());
            ctx.set_register_annotation(m_res, s.str());
        }
    };

    instruction * instruction::mk_filter_interpreted_and_project(reg_idx reg, app_ref & condition,
        unsigned col_cnt, const unsigned * removed_cols, reg_idx result) {
        return alloc(instr_filter_interpreted_and_project, reg, condition, col_cnt, removed_cols, result);
    }


    class instr_union : public instruction {
        reg_idx m_src;
        reg_idx m_tgt;
        reg_idx m_delta;
        bool m_widen; //if true, widening is performed intead of an union
    public:
        instr_union(reg_idx src, reg_idx tgt, reg_idx delta, bool widen)
            : m_src(src), m_tgt(tgt), m_delta(delta), m_widen(widen) {}
        virtual bool perform(execution_context & ctx) {
            TRACE("dl", tout << "union " << m_src << " into " << m_tgt 
              << " " << ctx.reg(m_src) << " " << ctx.reg(m_tgt) << "\n";);
            log_verbose(ctx);
            if (!ctx.reg(m_src)) {
                return true;
            }
            ++ctx.m_stats.m_union;
            relation_base & r_src = *ctx.reg(m_src);
            if (!ctx.reg(m_tgt)) {
                relation_base * new_tgt = r_src.get_plugin().mk_empty(r_src);
                ctx.set_reg(m_tgt, new_tgt);
            }
            relation_base & r_tgt = *ctx.reg(m_tgt);
            if (m_delta!=execution_context::void_register && !ctx.reg(m_delta)) {
                relation_base * new_delta = r_tgt.get_plugin().mk_empty(r_tgt);
                ctx.set_reg(m_delta, new_delta);
            }
            relation_base * r_delta = (m_delta!=execution_context::void_register) ? ctx.reg(m_delta) : 0;

            relation_union_fn * fn;

            if (r_delta) {
                if (!find_fn(r_tgt, r_src, *r_delta, fn)) {
                    if (m_widen) {
                        fn = r_src.get_manager().mk_widen_fn(r_tgt, r_src, r_delta);
                    }
                    else {
                        fn = r_src.get_manager().mk_union_fn(r_tgt, r_src, r_delta);
                    }
                    if (!fn) {
                        std::stringstream sstm;
                        sstm << "trying to perform unsupported union operation on relations of kinds ";
                        sstm << r_tgt.get_plugin().get_name() << ", " << r_src.get_plugin().get_name() << " and ";
                        sstm << r_delta->get_plugin().get_name();
                        throw default_exception(sstm.str());
                    }
                    store_fn(r_tgt, r_src, *r_delta, fn);
                }
            }
            else {
                if (!find_fn(r_tgt, r_src, fn)) {
                    if (m_widen) {
                        fn = r_src.get_manager().mk_widen_fn(r_tgt, r_src, 0);
                    }
                    else {
                        fn = r_src.get_manager().mk_union_fn(r_tgt, r_src, 0);
                    }
                    if (!fn) {
                        std::stringstream sstm;
                        sstm << "trying to perform unsupported union operation on relations of kinds "
                             << r_tgt.get_plugin().get_name() << " and "
                             << r_src.get_plugin().get_name();
                        throw default_exception(sstm.str());
                    }
                    store_fn(r_tgt, r_src, fn);
                }
            }

            SASSERT(r_src.get_signature().size() == r_tgt.get_signature().size());
            TRACE("dl_verbose", r_tgt.display(tout <<"pre-union:"););

            (*fn)(r_tgt, r_src, r_delta);

            TRACE("dl_verbose", 
                r_src.display(tout <<"src:");
                r_tgt.display(tout <<"post-union:");
                if (r_delta) {
                    r_delta->display(tout <<"delta:");
                });

            if (r_delta && r_delta->fast_empty()) {
                ctx.make_empty(m_delta);
            }

            return true;
        }
        virtual void make_annotations(execution_context & ctx) {
            std::string str = "union";
            if (!ctx.get_register_annotation(m_tgt, str)) {
                ctx.set_register_annotation(m_tgt, "union");
            }
            if (m_delta != execution_context::void_register) {
                str = "delta of " + str;
            }
            ctx.set_register_annotation(m_delta, str);            
        }
        virtual void display_head_impl(execution_context const& ctx, std::ostream & out) const {
            out << (m_widen ? "widen " : "union ") << m_src << " into " << m_tgt;
            if (m_delta!=execution_context::void_register) {
                out << " with delta " << m_delta;
            }
        }
    };

    instruction * instruction::mk_union(reg_idx src, reg_idx tgt, reg_idx delta) {
        return alloc(instr_union, src, tgt, delta, false);
    }

    instruction * instruction::mk_widen(reg_idx src, reg_idx tgt, reg_idx delta) {
        return alloc(instr_union, src, tgt, delta, true);
    }


    class instr_project_rename : public instruction {
        typedef unsigned_vector column_vector;
        bool m_projection;
        reg_idx m_src;
        column_vector m_cols;
        reg_idx m_tgt;
    public:
        instr_project_rename(bool projection, reg_idx src, unsigned col_cnt, const unsigned * cols, 
            reg_idx tgt) : m_projection(projection), m_src(src), 
            m_cols(col_cnt, cols), m_tgt(tgt) {}
        virtual bool perform(execution_context & ctx) {
            log_verbose(ctx);
            if (!ctx.reg(m_src)) {
                ctx.make_empty(m_tgt);
                return true;
            }
        
            ++ctx.m_stats.m_project_rename;
            relation_transformer_fn * fn;
            relation_base & r_src = *ctx.reg(m_src);
            if (!find_fn(r_src, fn)) {
                if (m_projection) {
                    fn = r_src.get_manager().mk_project_fn(r_src, m_cols.size(), m_cols.c_ptr());
                }
                else {
                    fn = r_src.get_manager().mk_rename_fn(r_src, m_cols.size(), m_cols.c_ptr());
                }
                if (!fn) {
                    std::stringstream sstm;
                    sstm << "trying to perform unsupported " << (m_projection ? "project" : "rename");
                    sstm << " operation on a relation of kind " << r_src.get_plugin().get_name();
                    throw default_exception(sstm.str());
                }
                store_fn(r_src, fn);
            }
            ctx.set_reg(m_tgt, (*fn)(r_src));

            return true;
        }
        virtual void display_head_impl(execution_context const& ctx, std::ostream & out) const {
            out << (m_projection ? "project " : "rename ") << m_src << " into " << m_tgt;
            out << (m_projection ? " deleting columns " : " with cycle ");
            print_container(m_cols, out);
        }
        virtual void make_annotations(execution_context & ctx) {
            std::stringstream s;
            std::string a = "rel_src";
            ctx.get_register_annotation(m_src, a);
            s << (m_projection ? "project " : "rename ") << a;
            ctx.set_register_annotation(m_tgt, s.str());
        }
    };

    instruction * instruction::mk_projection(reg_idx src, unsigned col_cnt, const unsigned * removed_cols, 
            reg_idx tgt) {
        return alloc(instr_project_rename, true, src, col_cnt, removed_cols, tgt);
    }
    instruction * instruction::mk_rename(reg_idx src, unsigned cycle_len, const unsigned * permutation_cycle, 
            reg_idx tgt) {
        return alloc(instr_project_rename, false, src, cycle_len, permutation_cycle, tgt);
    }

    class instr_multiary_join_project : public instruction {
      typedef unsigned_vector column_vector;
      reg_idx m_result;
      vector<column_vector> m_cols1;
      vector<column_vector> m_cols2;
      vector<column_vector> m_removed_cols;
      svector<reg_idx> m_regs;
    public:
      instr_multiary_join_project(const reg_idx * tail_regs, unsigned pt_len,
        const vector<variable_intersection> & join_vars,
        const vector<unsigned_vector> & removed_cols,
        reg_idx result_reg) : m_result(result_reg) {
        SASSERT(pt_len > 2);
        SASSERT(pt_len == join_vars.size() + 1);
        // copying stuff
        vector<variable_intersection>::const_iterator it = join_vars.begin(), end = join_vars.end();
        unsigned i = 0;
        m_regs.push_back(tail_regs[i]);
        for (; it != end; ++it) {
          m_cols1.push_back(column_vector(it->size(), it->get_cols1()));
          m_cols2.push_back(column_vector(it->size(), it->get_cols2()));
          m_removed_cols.push_back(column_vector(removed_cols[i].size(), removed_cols[i].c_ptr()));
          m_regs.push_back(tail_regs[i + 1]);
          i++;
        }
      }
      virtual bool perform(execution_context & ctx) {
        log_verbose(ctx);

        // check if any of the regs contains an empty relation
        ++ctx.m_stats.m_multiary_join;
        svector<reg_idx>::const_iterator it = m_regs.begin(), end = m_regs.end();
        for (; it != end; ++it) {
          if (!ctx.reg(*it)) {
            ctx.make_empty(m_result);
            return true;
          }
        }

        reg_idx join_reg1 = m_regs[0];
        it = m_regs.begin() + 1, end = m_regs.end();
        unsigned i = 0;
        for (; it != end; ++it) {
          reg_idx join_reg2 = *it;
          const relation_base & r1 = *ctx.reg(join_reg1);
          const relation_base & r2 = *ctx.reg(join_reg2);
          relation_join_fn * fn;
          /* slower with caching
          if (!find_fn(r1, r2, i, fn)) {*/
          fn = r1.get_manager().mk_join_project_fn(r1, r2, m_cols1[i], m_cols2[i], m_removed_cols[i]);
          if (!fn) {
            throw default_exception("trying to perform unsupported join operation on relations of kinds %s and %s",
              r1.get_plugin().get_name().bare_str(), r2.get_plugin().get_name().bare_str());
          }
          /*  store_fn(r1, r2, i, fn);
          }*/
          /*
          TRACE("dl", tout << "input: ";
            r1.get_signature().output(ctx.get_rel_context().get_manager(), tout);
          tout << ":" << r1.get_size_estimate_rows() << " x ";
          r2.get_signature().output(ctx.get_rel_context().get_manager(), tout);
          tout << ":" << r2.get_size_estimate_rows() << " ->\n";);
          */

          ctx.set_reg(m_result, (*fn)(r1, r2));
          /*
          TRACE("dl", tout << "output: ";
            ctx.reg(m_result)->get_signature().output(ctx.get_rel_context().get_manager(), tout);
          tout << ":" << ctx.reg(m_result)->get_size_estimate_rows() << "\n";);
          */

          if (ctx.reg(m_result)->fast_empty()) {
            ctx.make_empty(m_result);
            return true;
          }

          join_reg1 = m_result;
          i++;
        }

        return true;
      }
      virtual void make_annotations(execution_context & ctx) {
        /*
        std::string a1 = "rel1", a2 = "rel2";
        ctx.get_register_annotation(m_rel1, a1);
        ctx.get_register_annotation(m_rel1, a1);
        ctx.set_register_annotation(m_res, "join " + a1 + " " + a2);
        */
      }
      virtual void display_head_impl(execution_context const & ctx, std::ostream & out) const {
        out << "multiary_join_project " << *m_regs.begin();
        svector<reg_idx>::const_iterator it = m_regs.begin() + 1, end = m_regs.end();
        unsigned i = 0;
        for (; it != end; ++it) {
          out << " ";
          print_container(m_cols1[i], out);
          out << " and ";
          print_container(m_cols2[i], out);
          out << " " << *it;
          i++;
        }
        out << " into " << m_result;
        out << " removing columns";
        svector<column_vector>::const_iterator remit = m_removed_cols.begin(), remend = m_removed_cols.end();
        for (; remit != remend; ++remit) {
          out << " ";
          print_container(*remit, out);
        }
      }
    };

    instruction * instruction::mk_multiary_join_project(const reg_idx * tail_regs, unsigned pt_len,
      const vector<variable_intersection> & join_vars, const vector<unsigned_vector> & removed_cols,
      reg_idx result_reg) {
      return alloc(instr_multiary_join_project, tail_regs, pt_len, join_vars, removed_cols, result_reg);
    }

    class instr_join_project : public instruction {
        typedef unsigned_vector column_vector;
        reg_idx m_rel1;
        reg_idx m_rel2;
        column_vector m_cols1;
        column_vector m_cols2;
        column_vector m_removed_cols;
        reg_idx m_res;
    public:
        instr_join_project(reg_idx rel1, reg_idx rel2, unsigned joined_col_cnt, const unsigned * cols1, 
            const unsigned * cols2, unsigned removed_col_cnt, const unsigned * removed_cols, reg_idx result)
            : m_rel1(rel1), m_rel2(rel2), m_cols1(joined_col_cnt, cols1), 
            m_cols2(joined_col_cnt, cols2), m_removed_cols(removed_col_cnt, removed_cols), m_res(result) {
        }
        virtual bool perform(execution_context & ctx) {
            log_verbose(ctx);            
            if (!ctx.reg(m_rel1) || !ctx.reg(m_rel2)) {
                ctx.make_empty(m_res);
                return true;
            }
            ++ctx.m_stats.m_join_project;
            relation_join_fn * fn;
            const relation_base & r1 = *ctx.reg(m_rel1);
            const relation_base & r2 = *ctx.reg(m_rel2);
            if (!find_fn(r1, r2, fn)) {
                fn = r1.get_manager().mk_join_project_fn(r1, r2, m_cols1, m_cols2, m_removed_cols);
                if (!fn) {
                    throw default_exception("trying to perform unsupported join-project operation on relations of kinds %s and %s",
                        r1.get_plugin().get_name().bare_str(), r2.get_plugin().get_name().bare_str());
                }
                store_fn(r1, r2, fn);
            }
            TRACE("dl", tout<<r1.get_size_estimate_rows()<<" x "<<r2.get_size_estimate_rows()<<" jp->\n";);
            ctx.set_reg(m_res, (*fn)(r1, r2));
            TRACE("dl",  tout<<ctx.reg(m_res)->get_size_estimate_rows()<<"\n";);
            if (ctx.reg(m_res)->fast_empty()) {
                ctx.make_empty(m_res);
            }
            return true;
        }
        virtual void display_head_impl(execution_context const& ctx, std::ostream & out) const {
            relation_base const* r1 = ctx.reg(m_rel1);
            relation_base const* r2 = ctx.reg(m_rel2);
            out << "join_project " << m_rel1;            
            if (r1) {
                out << ":" << r1->num_columns();
                out << "-" << r1->get_size_estimate_rows();
            }
            print_container(m_cols1, out);
            out << " and " << m_rel2;
            if (r2) {
                out << ":" << r2->num_columns();
                out << "-" << r2->get_size_estimate_rows();
            }
            print_container(m_cols2, out);
            out << " into " << m_res << " removing columns ";
            print_container(m_removed_cols, out);
        }
        virtual void make_annotations(execution_context & ctx) {
            std::string s1 = "rel1", s2 = "rel2";
            ctx.get_register_annotation(m_rel1, s1);
            ctx.get_register_annotation(m_rel2, s2);
            ctx.set_register_annotation(m_res, "join project " + s1 + " " + s2);            
        }
    };

    instruction * instruction::mk_join_project(reg_idx rel1, reg_idx rel2, unsigned joined_col_cnt,
        const unsigned * cols1, const unsigned * cols2, unsigned removed_col_cnt, 
        const unsigned * removed_cols, reg_idx result) {
            return alloc(instr_join_project, rel1, rel2, joined_col_cnt, cols1, cols2, removed_col_cnt,
                removed_cols, result);
    }


    class instr_select_equal_and_project : public instruction {
        reg_idx m_src;
        reg_idx m_result;
        app_ref m_value;
        unsigned m_col;
    public:
        instr_select_equal_and_project(ast_manager & m, reg_idx src, const relation_element & value, 
            unsigned col, reg_idx result)
            : m_src(src), m_result(result), m_value(value, m), m_col(col) {
            // [Leo]: does not compile on gcc
            // TRACE("dl", tout << "src:"  << m_src << " result: " << m_result << " value:" << m_value << " column:" << m_col << "\n";);
        }

        virtual bool perform(execution_context & ctx) {
            log_verbose(ctx);
            if (!ctx.reg(m_src)) {
                ctx.make_empty(m_result);
                return true;
            }           
            ++ctx.m_stats.m_select_equal_project;
            relation_transformer_fn * fn;
            relation_base & r = *ctx.reg(m_src);
            if (!find_fn(r, fn)) {
                fn = r.get_manager().mk_select_equal_and_project_fn(r, m_value, m_col);
                if (!fn) {
                    throw default_exception(
                        "trying to perform unsupported select_equal_and_project operation on a relation of kind %s",
                        r.get_plugin().get_name().bare_str());
                }
                store_fn(r, fn);
            }
            ctx.set_reg(m_result, (*fn)(r));

            if (ctx.reg(m_result)->fast_empty()) {
                ctx.make_empty(m_result);
            }
            return true;
        }
        virtual void display_head_impl(execution_context const& ctx, std::ostream & out) const {
            out << "select_equal_and_project " << m_src <<" into " << m_result << " col: " << m_col 
                << " val: " << ctx.get_rel_context().get_rmanager().to_nice_string(m_value);
        }
        virtual void make_annotations(execution_context & ctx) {
            std::stringstream s;
            std::string s1 = "src";
            ctx.get_register_annotation(m_src, s1);
            s << "select equal project col " << m_col << " val: " 
              << ctx.get_rel_context().get_rmanager().to_nice_string(m_value) << " " << s1;
            ctx.set_register_annotation(m_result, s.str());            
        }
    };

    instruction * instruction::mk_select_equal_and_project(ast_manager & m, reg_idx src, 
            const relation_element & value, unsigned col, reg_idx result) {
        return alloc(instr_select_equal_and_project, m, src, value, col, result);
    }


    class instr_filter_by_negation : public instruction {
        typedef unsigned_vector column_vector;
        reg_idx m_tgt;
        reg_idx m_neg_rel;
        column_vector m_cols1;
        column_vector m_cols2;
    public:
        instr_filter_by_negation(reg_idx tgt, reg_idx neg_rel, unsigned col_cnt, const unsigned * cols1, 
            const unsigned * cols2)
            : m_tgt(tgt), m_neg_rel(neg_rel), m_cols1(col_cnt, cols1), m_cols2(col_cnt, cols2) {}
        virtual bool perform(execution_context & ctx) {
            log_verbose(ctx);            
            if (!ctx.reg(m_tgt) || !ctx.reg(m_neg_rel)) {
                return true;
            }
            ++ctx.m_stats.m_filter_by_negation;

            relation_intersection_filter_fn * fn;
            relation_base & r1 = *ctx.reg(m_tgt);
            const relation_base & r2 = *ctx.reg(m_neg_rel);
            if (!find_fn(r1, r2, fn)) {
                fn = r1.get_manager().mk_filter_by_negation_fn(r1, r2, m_cols1.size(), m_cols1.c_ptr(), m_cols2.c_ptr());
                if (!fn) {
                    std::stringstream sstm;
                    sstm << "trying to perform unsupported filter_by_negation on relations of kinds ";
                    sstm << r1.get_plugin().get_name() << " and " << r2.get_plugin().get_name();
                    throw default_exception(sstm.str());
                }
                store_fn(r1, r2, fn);
            }
            (*fn)(r1, r2);

            if (r1.fast_empty()) {
                ctx.make_empty(m_tgt);
            }
            return true;
        }
        virtual void display_head_impl(execution_context const& ctx, std::ostream & out) const {
            out << "filter_by_negation on " << m_tgt;
            print_container(m_cols1, out);
            out << " with " << m_neg_rel;
            print_container(m_cols2, out);
            out << " as the negated table";
        }
        virtual void make_annotations(execution_context & ctx) {
            std::string s = "negated relation";
            ctx.get_register_annotation(m_neg_rel, s);
            ctx.set_register_annotation(m_tgt, "filter by negation " + s);            
        }
    };

    instruction * instruction::mk_filter_by_negation(reg_idx tgt, reg_idx neg_rel, unsigned col_cnt,
            const unsigned * cols1, const unsigned * cols2) {
        return alloc(instr_filter_by_negation, tgt, neg_rel, col_cnt, cols1, cols2);
    }

        
    class instr_mk_unary_singleton : public instruction {
        relation_signature m_sig;
        func_decl* m_pred;
        reg_idx m_tgt;
        relation_fact m_fact;
    public:
        instr_mk_unary_singleton(ast_manager & m, func_decl* head_pred, const relation_sort & s, const relation_element & val, 
            reg_idx tgt) : m_pred(head_pred), m_tgt(tgt), m_fact(m) {
            m_sig.push_back(s);
            m_fact.push_back(val);
        }
        virtual bool perform(execution_context & ctx) {
          TRACE("dl", tout << "mk_unary_singleton into " << m_tgt << " sort:"
            << ctx.get_rel_context().get_rmanager().to_nice_string(m_sig[0]) << " val:"
            << ctx.get_rel_context().get_rmanager().to_nice_string(m_sig[0], m_fact[0]););
            log_verbose(ctx);            
            ++ctx.m_stats.m_unary_singleton;
            relation_base * rel = ctx.get_rel_context().get_rmanager().mk_empty_relation(m_sig, m_pred);
            rel->add_fact(m_fact);
            ctx.set_reg(m_tgt, rel);
            return true;
        }
        virtual void display_head_impl(execution_context const& ctx, std::ostream & out) const {
            out << "mk_unary_singleton into " << m_tgt << " sort:" 
                << ctx.get_rel_context().get_rmanager().to_nice_string(m_sig[0]) << " val:" 
                << ctx.get_rel_context().get_rmanager().to_nice_string(m_sig[0], m_fact[0]);
        }
        virtual void make_annotations(execution_context & ctx) {
            std::string s;
            if (!ctx.get_register_annotation(m_tgt, s)) {
                ctx.set_register_annotation(m_tgt, "mk unary singleton");
            }
        }
    };

    instruction * instruction::mk_unary_singleton(ast_manager & m, func_decl* head_pred, const relation_sort & s, 
            const relation_element & val, reg_idx tgt) {
        return alloc(instr_mk_unary_singleton, m, head_pred, s, val, tgt);
    }


    class instr_mk_total : public instruction {
        relation_signature m_sig;
        func_decl* m_pred;
        reg_idx m_tgt;
    public:
        instr_mk_total(const relation_signature & sig, func_decl* p, reg_idx tgt) : m_sig(sig), m_pred(p), m_tgt(tgt) {}
        virtual bool perform(execution_context & ctx) {
          TRACE("dl", tout << "mk_total into " << m_tgt << " sort:"
            << ctx.get_rel_context().get_rmanager().to_nice_string(m_sig););
            log_verbose(ctx);            
            ++ctx.m_stats.m_total;
            ctx.set_reg(m_tgt, ctx.get_rel_context().get_rmanager().mk_full_relation(m_sig, m_pred));
            return true;
        }
        virtual void display_head_impl(execution_context const& ctx, std::ostream & out) const {
            out << "mk_total into " << m_tgt << " sort:" 
                << ctx.get_rel_context().get_rmanager().to_nice_string(m_sig);
        }
        virtual void make_annotations(execution_context & ctx) {
            std::string s;
            if (!ctx.get_register_annotation(m_tgt, s)) {
                ctx.set_register_annotation(m_tgt, "mk_total");
            }
        }
    };

    instruction * instruction::mk_total(const relation_signature & sig, func_decl* pred, reg_idx tgt) {
        return alloc(instr_mk_total, sig, pred, tgt);
    }

    class instr_mark_saturated : public instruction {
        func_decl_ref m_pred;
    public:
        instr_mark_saturated(ast_manager & m, func_decl * pred) 
            : m_pred(pred, m) {}
        virtual bool perform(execution_context & ctx) {
            log_verbose(ctx);            
            ctx.get_rel_context().get_rmanager().mark_saturated(m_pred);
            return true;
        }
        virtual void display_head_impl(execution_context const& ctx, std::ostream & out) const {
            out << "mark_saturated " << m_pred->get_name().bare_str();
        }
        virtual void make_annotations(execution_context & ctx) {            
        }
    };

    instruction * instruction::mk_mark_saturated(ast_manager & m, func_decl * pred) {
        return alloc(instr_mark_saturated, m, pred);
    }

    class instr_assert_signature : public instruction {
        relation_signature m_sig;
        reg_idx m_tgt;
    public:
        instr_assert_signature(const relation_signature & s, reg_idx tgt) 
            : m_sig(s), m_tgt(tgt) {}
        virtual bool perform(execution_context & ctx) {
            log_verbose(ctx);            
            if (ctx.reg(m_tgt)) {
                SASSERT(ctx.reg(m_tgt)->get_signature()==m_sig);
            }
            return true;
        }
        virtual void display_head_impl(execution_context const& ctx, std::ostream & out) const {
            out << "instr_assert_signature of " << m_tgt << " signature:";
            print_container(m_sig, out);
        }
        virtual void make_annotations(execution_context & ctx) {
            std::string s;
            if (!ctx.get_register_annotation(m_tgt, s)) {
                ctx.set_register_annotation(m_tgt, "assert signature");
            }
        }
    };
    
    instruction * instruction::mk_assert_signature(const relation_signature & s, reg_idx tgt) {
        return alloc(instr_assert_signature, s, tgt);
    }

    extern compiler * g_compiler;
    class instr_exec : public instruction {
      rule * r;
      reg_idx head_reg;
      svector<reg_idx> tail_regs;
      reg_idx delta_reg;
      bool use_widening;
      instruction_block acc;
    private:

      void apply_negative_predicate(expr_ref_vector & pos_expr, unsigned & pos_reg, unsigned neg_index, bool & dealloc, ast_manager & m, execution_context & ctx) {
        //enforce negative predicates
        app * neg_app = r->get_tail(neg_index);
        func_decl * neg_pred = neg_app->get_decl();
        variable_intersection neg_intersection(m);
        neg_intersection.populate(pos_expr, neg_app);
        unsigned_vector t_cols(neg_intersection.size(), neg_intersection.get_cols1());
        unsigned_vector neg_cols(neg_intersection.size(), neg_intersection.get_cols2());
        TRACE("dl_query_plan", tout << "neg_app " << mk_pp(neg_app, g_compiler->m_context.get_manager()) << "\n";);
        unsigned neg_len = neg_app->get_num_args();
        for (unsigned i = 0; i < neg_len; i++) {
          expr * e = neg_app->get_arg(i);
          if (is_var(e)) {
            continue;
          }
          SASSERT(is_app(e));
          relation_sort arg_sort;
          g_compiler->m_context.get_rel_context()->get_rmanager().from_predicate(neg_pred, i, arg_sort);
          g_compiler->make_add_constant_column(r->get_head()->get_decl(), pos_reg, arg_sort, to_app(e), pos_reg, dealloc, ctx, acc);

          t_cols.push_back(pos_expr.size());
          neg_cols.push_back(i);
          pos_expr.push_back(e);
        }
        SASSERT(t_cols.size() == neg_cols.size());
        reg_idx neg_reg = g_compiler->m_pred_regs.find(neg_pred);
        acc.push_back(instruction::mk_filter_by_negation(pos_reg, neg_reg, t_cols.size(),
          t_cols.c_ptr(), neg_cols.c_ptr()));
        dealloc = true;
      }

      void make_remaining_negation(func_decl * head_pred, const unsigned_vector & remaining_neg_tail,
        expr_ref_vector & res_expr, reg_idx & res_reg, bool & dealloc, execution_context & ctx) {

        // add at least one column for the negative filter
        // lengths in original rule (DON'T USE res_expr.size())
        if (!remaining_neg_tail.empty() && res_reg == execution_context::void_register) {
          relation_signature empty_signature;
          g_compiler->make_full_relation(head_pred, empty_signature, res_reg, ctx, acc);
        }

        //enforce negative predicates
        unsigned_vector::const_iterator rem_it = remaining_neg_tail.begin(), rem_end = remaining_neg_tail.end();
        for (; rem_it != rem_end; ++rem_it) {
          unsigned j = *rem_it;
          app * neg_tail = r->get_tail(j);
          func_decl * neg_pred = neg_tail->get_decl();
          variable_intersection neg_intersection(g_compiler->m_context.get_manager());
          neg_intersection.populate(res_expr, neg_tail);
          unsigned_vector t_cols(neg_intersection.size(), neg_intersection.get_cols1());
          unsigned_vector neg_cols(neg_intersection.size(), neg_intersection.get_cols2());

          unsigned neg_len = neg_tail->get_num_args();
          for (unsigned i = 0; i < neg_len; i++) {
            expr * e = neg_tail->get_arg(i);
            if (is_var(e)) {
              continue;
            }
            SASSERT(is_app(e));
            relation_sort arg_sort;
            g_compiler->m_context.get_rel_context()->get_rmanager().from_predicate(neg_pred, i, arg_sort);
            g_compiler->make_add_constant_column(head_pred, res_reg, arg_sort, to_app(e), res_reg, dealloc, ctx, acc);

            t_cols.push_back(res_expr.size());
            neg_cols.push_back(i);
            res_expr.push_back(e);
          }
          SASSERT(t_cols.size() == neg_cols.size());

          reg_idx neg_reg = g_compiler->m_pred_regs.find(neg_pred);
          if (!dealloc)
            g_compiler->make_clone(res_reg, res_reg, acc);
          acc.push_back(instruction::mk_filter_by_negation(res_reg, neg_reg, t_cols.size(),
            t_cols.c_ptr(), neg_cols.c_ptr()));
          dealloc = true;
        }
      }

      void do_remaining_negation(const unsigned_vector & remaining_neg_tail,
        func_decl * head_pred, vector<int2ints> & var_indexes, bool &dealloc, ast_manager & m,
        vector<expr_ref_vector> & res_preds, svector<reg_idx> &res_regs, execution_context & ctx) {
        SASSERT(!res_preds.empty()); // because join_project always adds a result
        /*if (res_preds.empty()) {
          expr_ref_vector res_expr(m);
          reg_idx res_reg = execution_context::void_register;
          var_indexes.push_back(int2ints());
          dealloc = false; // TODO ? that's how it goes in original case

          g_compiler->add_unbound_columns_for_negation(r, head_pred, res_reg, res_expr, var_indexes[0], dealloc, ctx, acc);
          //make_negation(head_pred, pt_len, ut_len, res_expr, res_reg, dealloc, ctx);
          res_preds.push_back(res_expr);
          res_regs.push_back(res_reg);
        }
        else {*/
        unsigned i = 0;
        for (vector<expr_ref_vector>::iterator it = res_preds.begin(), end = res_preds.end();
          it != end; ++it, ++i) {
          expr_ref_vector &res_expr = *it;
          reg_idx &res_reg = res_regs[i];
          g_compiler->add_unbound_columns_for_negation(r, head_pred, res_reg, res_expr, var_indexes[i], dealloc, ctx, acc);
          make_remaining_negation(head_pred, remaining_neg_tail, res_expr, res_reg, dealloc, ctx);
        }
        //}
      }

      void compute_var_indexes(const expr_ref_vector &pred, int2ints &var_indexes) {
        //enforce equality to constants
        unsigned len = pred.size();
        for (unsigned i = 0; i < len; i++) {
          expr * exp = pred.get(i);
          if (is_var(exp)) {
            unsigned var_idx = to_var(exp)->get_idx();
            int2ints::entry * e = var_indexes.insert_if_not_there2(var_idx, unsigned_vector());
            e->get_data().m_value.push_back(i);
          }
        }

        TRACE("dl", for (int2ints::iterator I = var_indexes.begin(), E = var_indexes.end();
        I != E; ++I) {
          tout << I->m_key << ": "; print_container(I->m_value, tout); tout << "\n";
        });
      }

      void do_var_binding(app_ref & filter_cond, func_decl * head_pred,
        expr_ref_vector & res_expr, reg_idx &res_reg, int2ints & var_indexes,
        expr_ref_vector & binding, bool & dealloc, ast_manager & m, execution_context &ctx) {

        g_compiler->m_free_vars(filter_cond);
        // create binding
        binding.resize(g_compiler->m_free_vars.size() + 1);
        for (unsigned v = 0; v < g_compiler->m_free_vars.size(); ++v) {
          if (!g_compiler->m_free_vars[v])
            continue;

          int2ints::entry * entry = var_indexes.find_core(v);
          unsigned src_col;
          if (entry) {
            src_col = entry->get_data().m_value.back();
          }
          else {
            TRACE("dl", tout << "v: " << v << " ADD_UNBOUND_COLUMN " << res_reg << " dealloc: " << dealloc << "\n";);
            // we have an unbound variable, so we add an unbound column for it
            relation_sort unbound_sort = g_compiler->m_free_vars[v];

            g_compiler->make_add_unbound_column(r, 0, head_pred, res_reg, unbound_sort, res_reg, dealloc, ctx, acc);
            src_col = res_expr.size();
            res_expr.push_back(m.mk_var(v, unbound_sort));

            entry = var_indexes.insert_if_not_there2(v, unsigned_vector());
            entry->get_data().m_value.push_back(src_col);
          }
          relation_sort var_sort = g_compiler->m_reg_signatures[res_reg][src_col];
          binding[g_compiler->m_free_vars.size() - v] = m.mk_var(src_col, var_sort);
        }
      }

      void do_remove_columns(expr_ref_vector &res_expr, int2ints & var_indexes, unsigned_vector &remove_columns) {
        unsigned_vector var_idx_to_remove;
        g_compiler->m_free_vars(r->get_head());
        for (int2ints::iterator I = var_indexes.begin(), E = var_indexes.end();
          I != E; ++I) {
          unsigned var_idx = I->m_key;
          if (!g_compiler->m_free_vars.contains(var_idx)) {
            unsigned_vector & cols = I->m_value;
            for (unsigned i = 0; i < cols.size(); ++i) {
              remove_columns.push_back(cols[i]);
            }
            var_idx_to_remove.push_back(var_idx);
          }
        }

        for (unsigned i = 0; i < var_idx_to_remove.size(); ++i) {
          var_indexes.remove(var_idx_to_remove[i]);
        }

        // update column idx for after projection state
        if (!remove_columns.empty()) {
          unsigned_vector offsets;
          offsets.resize(res_expr.size(), 0);

          for (unsigned i = 0; i < remove_columns.size(); ++i) {
            for (unsigned col = remove_columns[i]; col < offsets.size(); ++col) {
              ++offsets[col];
            }
          }

          for (int2ints::iterator I = var_indexes.begin(), E = var_indexes.end();
            I != E; ++I) {
            unsigned_vector & cols = I->m_value;
            for (unsigned i = 0; i < cols.size(); ++i) {
              cols[i] -= offsets[cols[i]];
            }
          }
        }
      }

      void apply_filter(expr_ref_vector & pos_expr, unsigned interpreted_index, reg_idx &pos_index, bool &dealloc, ast_manager & m, execution_context & ctx) {
        // add unbounded columns for interpreted filter
        expr_ref_vector binding(m);

        app_ref filter_cond(to_app(r->get_tail(interpreted_index)), m);

        int2ints var_indexes;
        unsigned expr_len = pos_expr.size();
        for (unsigned i = 0; i < expr_len; i++) {
          expr * exp = pos_expr[i].get();
          if (is_var(exp)) {
            unsigned var_num = to_var(exp)->get_idx();
            int2ints::entry * e = var_indexes.insert_if_not_there2(var_num, unsigned_vector());
            e->get_data().m_value.push_back(i);
          }
        }

        
        g_compiler->m_free_vars(filter_cond);
        // create binding
        binding.resize(g_compiler->m_free_vars.size() + 1);
        for (unsigned v = 0; v < g_compiler->m_free_vars.size(); ++v) {
          if (!g_compiler->m_free_vars[v])
            continue;

          int2ints::entry * entry = var_indexes.find_core(v);
          unsigned src_col;
          if (entry) {
            src_col = entry->get_data().m_value.back();
          }
          else {
            SASSERT(false); // we only choose this positive index because there was an intersection between interpreted tail and pos expr
            //TRACE("dl", tout << "v: " << v << " ADD_UNBOUND_COLUMN " << res_reg << " dealloc: " << dealloc << "\n";);
            //// we have an unbound variable, so we add an unbound column for it
            //relation_sort unbound_sort = g_compiler->m_free_vars[v];

            //g_compiler->make_add_unbound_column(r, 0, head_pred, res_reg, unbound_sort, res_reg, dealloc, ctx, acc);
            //src_col = res_expr.size();
            //res_expr.push_back(m.mk_var(v, unbound_sort));

            //entry = var_indexes.insert_if_not_there2(v, unsigned_vector());
            //entry->get_data().m_value.push_back(src_col);
          }
          relation_sort var_sort = g_compiler->m_reg_signatures[pos_index][src_col];
          binding[g_compiler->m_free_vars.size() - v] = m.mk_var(src_col, var_sort);
        }

        // check if there are any columns to remove
        //unsigned_vector remove_columns;
        //do_remove_columns(res_expr, var_indexes, remove_columns);

        expr_ref renamed(m);
        g_compiler->m_context.get_var_subst()(filter_cond, binding.size(), binding.c_ptr(), renamed);
        app_ref app_renamed(to_app(renamed), m);
        //if (remove_columns.empty()) {
          //if (!dealloc)
          //  g_compiler->make_clone(res_reg, res_reg, acc);
        acc.push_back(instruction::mk_filter_interpreted(pos_index, app_renamed));
        //}
        //else {
        //  std::sort(remove_columns.begin(), remove_columns.end());
        //  g_compiler->make_filter_interpreted_and_project(res_reg, app_renamed, remove_columns, res_reg, dealloc, acc);
        //}

      }


      void make_filter(expr_ref_vector &res_expr, ptr_vector<expr> &interpreted_tail, func_decl * head_pred,
        int2ints & var_indexes, reg_idx &res_reg, bool &dealloc, ast_manager & m, execution_context & ctx) {
        // add unbounded columns for interpreted filter
        expr_ref_vector binding(m);

        app_ref filter_cond(interpreted_tail.size() == 1 ? to_app(interpreted_tail.back()) : m.mk_and(interpreted_tail.size(), interpreted_tail.c_ptr()), m);
        do_var_binding(filter_cond, head_pred, res_expr, res_reg, var_indexes, binding, dealloc, m, ctx);

        // check if there are any columns to remove
        unsigned_vector remove_columns;
        do_remove_columns(res_expr, var_indexes, remove_columns);

        expr_ref renamed(m);
        g_compiler->m_context.get_var_subst()(filter_cond, binding.size(), binding.c_ptr(), renamed);
        app_ref app_renamed(to_app(renamed), m);
        if (remove_columns.empty()) {
          if (!dealloc)
            g_compiler->make_clone(res_reg, res_reg, acc);
          acc.push_back(instruction::mk_filter_interpreted(res_reg, app_renamed));
        }
        else {
          std::sort(remove_columns.begin(), remove_columns.end());
          g_compiler->make_filter_interpreted_and_project(res_reg, app_renamed, remove_columns, res_reg, dealloc, acc);
        }

      }

      void do_remaining_filter(const unsigned_vector & remaining_neg_tail,
        func_decl * head_pred, vector<int2ints> & var_indexes, bool &dealloc, ast_manager & m,
        vector<expr_ref_vector> & res_preds, svector<reg_idx> &res_regs, execution_context & ctx) {

        ptr_vector<expr> interpreted_tail;
        unsigned_vector::const_iterator rem_it = remaining_neg_tail.begin(), rem_end = remaining_neg_tail.end();
        for (; rem_it != rem_end; ++rem_it) {
          interpreted_tail.push_back(r->get_tail(*rem_it));
        }
        SASSERT(!res_preds.empty()); // because join_project always adds a result
        /*if (res_preds.empty()) {
          if (!interpreted_tail.empty()) {
            expr_ref_vector res_expr(m);
            reg_idx res_reg = execution_context::void_register;
            var_indexes.push_back(int2ints());
            dealloc = false; // TODO ? that's how it goes in original case

            make_filter(res_expr, interpreted_tail, head_pred, var_indexes[0], res_reg, dealloc, m, ctx);

            res_preds.push_back(res_expr);
            res_regs.push_back(res_reg);
            dealloc = true;
          }
        }
        else {*/
        if (!interpreted_tail.empty()) {
          unsigned i = 0;
          for (vector<expr_ref_vector>::iterator it = res_preds.begin(), end = res_preds.end();
            it != end; ++it, ++i) {
            expr_ref_vector &res_expr = *it;
            reg_idx &res_reg = res_regs[i];

            make_filter(res_expr, interpreted_tail, head_pred, var_indexes[i], res_reg, dealloc, m, ctx);

            dealloc = true;
          }
        }
        //}
      }
      
      void do_join_project(unsigned pt_len, 
        func_decl * head_pred, vector<int2ints> & var_indexes,
        bool &dealloc, ast_manager & m, vector<expr_ref_vector> & res_preds, svector<reg_idx> &res_regs,
        const unsigned_vector & remaining_negated_tail,
        const unsigned_vector & remaining_interpreted_tail,
        execution_context & ctx) {
        // used for computing whether col equality needs to be established
        unsigned_vector belongs_to;
        unsigned_vector offsets;

        reg_idx single_res;
        expr_ref_vector single_res_expr(m);
        int2ints single_var_indexes;

        g_compiler->compile_join_project(r, remaining_negated_tail, remaining_interpreted_tail, res_preds, res_regs, m, pt_len,
          belongs_to, single_res, single_res_expr, dealloc, acc);

        res_preds.reset();
        res_regs.reset();
        var_indexes.reset();

        {
          //enforce equality to constants
          unsigned srlen = single_res_expr.size();
          SASSERT((single_res == execution_context::void_register) ? (srlen == 0) : (srlen == g_compiler->m_reg_signatures[single_res].size()));
          for (unsigned i = 0; i<srlen; i++) {
            expr * exp = single_res_expr[i].get();
            if (is_app(exp)) {
              SASSERT(g_compiler->m_context.get_decl_util().is_numeral_ext(exp));
              relation_element value = to_app(exp);
              if (!dealloc)
                g_compiler->make_clone(single_res, single_res, acc);
              acc.push_back(instruction::mk_filter_equal(g_compiler->m_context.get_manager(), single_res, value, i));
              dealloc = true;
            }
            else {
              SASSERT(is_var(exp));
              unsigned var_num = to_var(exp)->get_idx();
              int2ints::entry * e = single_var_indexes.insert_if_not_there2(var_num, unsigned_vector());
              e->get_data().m_value.push_back(i);
            }
          }
        }
        //enforce equality of columns
        int2ints::iterator vit = single_var_indexes.begin();
        int2ints::iterator vend = single_var_indexes.end();
        for (; vit != vend; ++vit) {
          int2ints::key_data & k = *vit;
          unsigned_vector & indexes = k.m_value;
          if (indexes.size() == 1) {
            continue;
          }
          SASSERT(indexes.size()>1);
          //If variable appears in multiple tails, the identicity will already be enforced by join.
          //(If behavior the join changes so that it is not enforced anymore, remove this
          //condition!)
          if (pt_len >= 2) {
            // only analyze belongs_to when we reach here, and only once
            if (offsets.empty()) {
              offsets.push_back(0);
              unsigned_vector::const_iterator belongs_it = belongs_to.begin(), belongs_end = belongs_to.end() - 1;
              for (unsigned i = 1; belongs_it != belongs_end; ++belongs_it, ++i) {
                if (*belongs_it != *(belongs_it + 1)) {
                  offsets.push_back(i);
                }
              }
              offsets.push_back(single_res_expr.size());
            }

            // check if all indexes are from a single predicate
            unsigned_vector::const_iterator it = offsets.begin(), end = offsets.end() - 1;
            bool var_in_single_interval = false;
            // if var_in_single_interval turns true, early exit
            for (; it != end && !var_in_single_interval; ++it) {
              int lower = *it, upper = *(it + 1);
              SASSERT(lower <= upper);
              int min_index = indexes[0], max_index = indexes.back();
              var_in_single_interval |= (lower <= min_index && max_index < upper);
            }
            if (!var_in_single_interval)
              continue;
          }
          if (!dealloc)
            g_compiler->make_clone(single_res, single_res, acc);
          acc.push_back(instruction::mk_filter_identical(single_res, indexes.size(), indexes.c_ptr()));
          dealloc = true;
        }

        res_preds.push_back(single_res_expr);
        res_regs.push_back(single_res);
        var_indexes.push_back(single_var_indexes);
      }

      void do_assemble(unsigned head_len, const app * h, func_decl * head_pred,
        const vector<int2ints> & pos_tail_var_indexes, bool dealloc, ast_manager & m,
        const vector<expr_ref_vector> & pos_tail_preds, const svector<reg_idx> &pos_tail_regs,
        execution_context & ctx) {
        SASSERT(pos_tail_preds.size() == 1);
        SASSERT(pos_tail_regs.size() == 1);
        SASSERT(pos_tail_var_indexes.size() == 1);
        {
          //put together the columns of head relation
          relation_signature & head_sig = g_compiler->m_reg_signatures[head_reg];
          svector<compiler::assembling_column_info> head_acis;
          unsigned_vector head_src_cols;
          for (unsigned i = 0; i<head_len; i++) {
            compiler::assembling_column_info aci;
            aci.domain = head_sig[i];

            expr * exp = h->get_arg(i);
            if (is_var(exp)) {
              unsigned var_num = to_var(exp)->get_idx();
              int2ints::entry * e = pos_tail_var_indexes[0].find_core(var_num);
              if (e) {
                unsigned_vector & binding_indexes = e->get_data().m_value;
                aci.kind = g_compiler->ACK_BOUND_VAR;
                aci.source_column = binding_indexes.back();
                SASSERT(aci.source_column < pos_tail_preds[0].size()); //we bind only to existing columns
                if (binding_indexes.size()>1) {
                  //if possible, we do not want multiple head columns
                  //point to a single column in the intermediate table,
                  //since then we would have to duplicate the column
                  //(and remove columns we did not point to at all)
                  binding_indexes.pop_back();
                }
              }
              else {
                aci.kind = g_compiler->ACK_UNBOUND_VAR;
                aci.var_index = var_num;
              }
            }
            else {
              SASSERT(is_app(exp));
              SASSERT(g_compiler->m_context.get_decl_util().is_numeral_ext(exp));
              aci.kind = g_compiler->ACK_CONSTANT;
              aci.constant = to_app(exp);
            }
            head_acis.push_back(aci);
          }
          SASSERT(head_acis.size() == head_len);

          SASSERT(pos_tail_regs.size() > 0);
          reg_idx new_head_reg;
          g_compiler->make_assembling_code(r, head_pred, pos_tail_regs[0], head_acis, new_head_reg, dealloc, ctx, acc);

          //update the head relation
          g_compiler->make_union(new_head_reg, head_reg, delta_reg, use_widening, acc);
          if (dealloc)
            g_compiler->make_dealloc_non_void(new_head_reg, acc);
        }
      }

      // Compute a map of variables to pos tail indexes in whose accompanying predicate the variable appears
      void compute_var_occurrences(unsigned pt_len,
        int2ints & pt_var_occurrences) {
        for (unsigned pos_index = 0; pos_index < pt_len; ++pos_index) {
          app * pred = r->get_tail(pos_index);
          for (unsigned arg_index = 0; arg_index < pred->get_num_args(); ++arg_index) {
            expr * e = r->get_tail(pos_index)->get_arg(arg_index);
            if (is_var(e)) {
              unsigned v = to_var(e)->get_idx();
              int2ints::entry * entry = pt_var_occurrences.find_core(v);
              if (!entry) {
                entry = pt_var_occurrences.insert_if_not_there2(v, unsigned_vector());
              }
              // Make sure that pos_index isn't inserted multiple times (e.g. f(x,x))
              // FIXME O(n), but can't have map of int_set
              if (!entry->get_data().m_value.contains(pos_index)) {
                entry->get_data().m_value.push_back(pos_index);
              }
            }
          }
        }

        int2ints::iterator it = pt_var_occurrences.begin(), end = pt_var_occurrences.end();
        TRACE("dl_query_plan",
          for (; it != end; ++it) {
            tout << it->m_key << ": ";
            print_container(it->m_value, tout);
            tout << "\n";
          }
        );
      }

      void pick_tail_indexes(unsigned start_index, unsigned end_index,
        const int2ints & pt_var_occurrences,
        ast_manager &m,
        int2ints &picks) {
        for (unsigned tail_index = start_index; tail_index < end_index; ++tail_index) {
          unsigned_vector tail_index_picks;
          app * pred = r->get_tail(tail_index);
          unsigned_vector vars;
          for (unsigned arg_index = 0; arg_index < pred->get_num_args(); ++arg_index) {
            expr * e = r->get_tail(tail_index)->get_arg(arg_index);
            if (is_var(e)) {
              vars.push_back(to_var(e)->get_idx());
            }
          }
          unsigned num_vars = vars.size();
          if (num_vars == 1) {
            int2ints::entry *entry = pt_var_occurrences.find_core(vars[0]);
            if (entry) {
              unsigned_vector::iterator vo_it = entry->get_data().m_value.begin(), vo_end = entry->get_data().m_value.end();
              for (; vo_it != vo_end; ++vo_it) {
                tail_index_picks.push_back(*vo_it);
                TRACE("dl_query_plan", tout << "tail index with size 1\n";);
              }
            }
          }
          else if (num_vars > 1) {
            // pick arbitrary variable that occurs in the neg/interpreted tail
            // to get a reduced list of positive indexes, which are candidates for 
            // subsuming the neg/interpreted tail
            int2ints::entry *entry = pt_var_occurrences.find_core(vars[0]);
            if (entry) {
              // do extra work, to see if pred is a subset of the predicate at pos_index
              unsigned_vector::iterator vo_it = entry->get_data().m_value.begin(), vo_end = entry->get_data().m_value.end();
              for (; vo_it != vo_end; ++vo_it) {
                reg_idx pos_index = *vo_it;
                variable_intersection intersect(m);
                intersect.populate(pred, r->get_tail(pos_index));
                if (intersect.size() == num_vars) {
                  tail_index_picks.push_back(pos_index);
                  TRACE("dl_query_plan", tout << "tail index with size " << num_vars << "\n";);
                }
              }
            }
          }

          if (!tail_index_picks.empty()) {
            picks.insert(tail_index, tail_index_picks);

            TRACE("dl_query_plan",
              tout << "picked regs ";
            print_container(tail_index_picks, tout);
            tout << " for " << mk_pp(r->get_tail(tail_index), g_compiler->m_context.get_manager()) << "\n";
            );
          }
        }
      }


      void make_query_plan(unsigned pt_len, unsigned ut_len, unsigned ft_len, ast_manager & m,
        int2ints & neg_picks, int2ints & interpreted_picks) {
        int2ints pt_var_occurrences;
        compute_var_occurrences(pt_len, pt_var_occurrences);
        TRACE("dl_query_plan", tout << "negated\n";);
        pick_tail_indexes(pt_len, ut_len, pt_var_occurrences, m, neg_picks);
        TRACE("dl_query_plan", tout << "interpreted\n";);
        pick_tail_indexes(ut_len, ft_len, pt_var_occurrences, m, interpreted_picks);
      }

      void reorder_negations(unsigned pt_len, unsigned ut_len, const int2ints & neg_picks, 
        vector<expr_ref_vector> & pos_tail_preds, svector<reg_idx> & pos_tail_regs, 
        unsigned_vector & remaining_negated_tail, int_set & tmp_regs,
        ast_manager & m, bool & dealloc, execution_context & ctx) {

        unsigned neg_applications = 0; // TODO just for debugging
        for (unsigned neg_index = pt_len; neg_index < ut_len; ++neg_index) {
          int2ints::entry *entry = neg_picks.find_core(neg_index);
          if (entry) {
            unsigned_vector apply_to = entry->get_data().m_value;
            unsigned_vector::iterator at_it = apply_to.begin(), at_end = apply_to.end();
            for (; at_it != at_end; ++at_it) {
              unsigned pos_index = *at_it;
              TRACE("dl_query_plan", tout << "pos_app " << mk_pp(r->get_tail(pos_index), m) << "\n";);
              reg_idx & pos_reg = pos_tail_regs[pos_index];
              // only need to clone if reg is in "original" positive tail
              if (!tmp_regs.contains(pos_reg)) {
                g_compiler->make_clone(pos_reg, pos_reg, acc);
                tmp_regs.insert(pos_reg);
              }
              apply_negative_predicate(pos_tail_preds[pos_index], pos_reg, neg_index, dealloc, m, ctx);
              TRACE("dl_stats", if (pt_len > 1) { tout << "after neg " << (ctx.reg(pos_reg) ? ctx.reg(pos_reg)->get_size_estimate_rows() : 0) << "\n"; });
            }
            neg_applications++;
          }
          else {
            remaining_negated_tail.push_back(neg_index);
          }
        }
        TRACE("dl_query_plan", tout << "neg applications: " << neg_applications << "\n";);
        SASSERT(neg_applications + remaining_negated_tail.size() == ut_len - pt_len);
      }

      void reorder_interpreted(unsigned ut_len, unsigned ft_len, const int2ints & interpreted_picks,
        vector<expr_ref_vector> & pos_tail_preds, svector<reg_idx> & pos_tail_regs,
        unsigned_vector & remaining_interpreted_tail, int_set & tmp_regs,
        ast_manager & m, bool & dealloc, execution_context & ctx) {

        unsigned interpreted_applications = 0; // TODO just for debugging
        for (unsigned interpreted_index = ut_len; interpreted_index < ft_len; ++interpreted_index) {
          int2ints::entry *entry = interpreted_picks.find_core(interpreted_index);
          if (entry) {
            unsigned_vector apply_to = entry->get_data().m_value;
            unsigned_vector::iterator at_it = apply_to.begin(), at_end = apply_to.end();
            for (; at_it != at_end; ++at_it) {
              unsigned pos_index = *at_it;
              TRACE("dl_query_plan", tout << "pos_app " << mk_pp(r->get_tail(pos_index), m) << "\n";);
              reg_idx & pos_reg = pos_tail_regs[pos_index];

              //TODO
              // only need to clone if reg is in "original" positive tail
              if (!tmp_regs.contains(pos_reg)) {
                g_compiler->make_clone(pos_reg, pos_reg, acc);
                tmp_regs.insert(pos_reg);
              }
              apply_filter(pos_tail_preds[pos_index], interpreted_index, pos_reg, dealloc, m, ctx);
            }
            interpreted_applications++;
          }
          else {
            remaining_interpreted_tail.push_back(interpreted_index);
          }

        }
        TRACE("dl_query_plan", tout << "interpreted applications: " << interpreted_applications << "\n";);
        SASSERT(interpreted_applications + remaining_interpreted_tail.size() == ft_len - ut_len);
      }

    public:
      instr_exec(rule * r, reg_idx head_reg, const reg_idx * regs,
        reg_idx delta_reg, bool use_widening)
        : r(r), head_reg(head_reg), delta_reg(delta_reg), use_widening(use_widening) {
        for (unsigned i = 0; i < r->get_positive_tail_size(); ++i) {
          tail_regs.push_back(regs[i]);
        }
      }

      virtual bool perform(execution_context & ctx) {

        TRACE("dl", tout << "RULE\n"; r->display(g_compiler->m_context, tout););
        TRACE("dl_stats", tout << "RULE\n"; r->display(g_compiler->m_context, tout););
        TRACE("dl_query_plan", tout << "RULE\n"; r->display(g_compiler->m_context, tout););
        // caching
        if (acc.num_instructions() != 0) {
          acc.reset(); // recomputing every time
        //  TRACE("dl", tout << "cache CODE\n"; acc.display(ctx, tout););
        //  acc.perform(ctx);
        //  return true;
        }
        ast_manager & m = g_compiler->m_context.get_manager();
        g_compiler->m_instruction_observer.start_rule(r);

        const app * h = r->get_head();
        unsigned head_len = h->get_num_args();
        func_decl * head_pred = h->get_decl();

        const unsigned pt_len = r->get_positive_tail_size();
        const unsigned ut_len = r->get_uninterpreted_tail_size();
        const unsigned ft_len = r->get_tail_size(); // full tail
        
        // whether to dealloc the previous result
        bool dealloc = true;

        // using expr_ref_vector instead of app* for updating tail predicates
        vector<expr_ref_vector> pos_tail_preds;
        svector<reg_idx>        pos_tail_regs;
        vector<int2ints>        pos_tail_var_indexes;
        // set up modifiable predicates / tmp registers / var_indexes
        for (unsigned i = 0; i < pt_len; ++i) {
          SASSERT(g_compiler->m_reg_signatures[tail_regs[i]].size() == r->get_tail(i)->get_num_args());
          expr_ref_vector res_expr = expr_ref_vector(g_compiler->m_context.get_manager(), r->get_tail(i)->get_num_args(), r->get_tail(i)->get_args());
          pos_tail_preds.push_back(res_expr);

          pos_tail_regs.push_back(tail_regs[i]);
          TRACE("dl_stats", if(pt_len > 1) {tout << "before join " << (ctx.reg(tail_regs[i]) ? ctx.reg(tail_regs[i])->get_size_estimate_rows() : 0) << "\n" << mk_pp(r->get_tail(i), m) << "\n";});

          int2ints var_indexes;
          pos_tail_var_indexes.push_back(var_indexes);
        }
        
        bool empty = false;
        svector<reg_idx>::iterator pt_it = pos_tail_regs.begin(), pt_end = pos_tail_regs.end();
        for (; pt_it != pt_end; ++pt_it) {
          if (!ctx.reg(*pt_it)) {
            empty = true;
            break;
          }
        }

        unsigned_vector remaining_negated_tail;
        unsigned_vector remaining_interpreted_tail;
        int_set tmp_regs;
        if (!empty && pt_len > 1 && ft_len - pt_len > 0) {
          int2ints neg_picks, interpreted_picks;
          make_query_plan(pt_len, ut_len, ft_len, m, neg_picks, interpreted_picks);

          reorder_negations(pt_len, ut_len, neg_picks, pos_tail_preds, pos_tail_regs, remaining_negated_tail, tmp_regs, m, dealloc, ctx);
          
          reorder_interpreted(ut_len, ft_len, interpreted_picks, pos_tail_preds, pos_tail_regs, remaining_interpreted_tail, tmp_regs, m, dealloc, ctx);
        }
        else {
          // No reordering before joins
          TRACE("dl_query_plan", tout << "EMPTY OR PT_LEN == 1\n";);
          for (unsigned neg_index = pt_len; neg_index < ut_len; ++neg_index) {
            remaining_negated_tail.push_back(neg_index);
          }
          SASSERT(remaining_negated_tail.size() == ut_len - pt_len);

          for (unsigned interpreted_index = ut_len; interpreted_index < ft_len; ++interpreted_index) {
            remaining_interpreted_tail.push_back(interpreted_index);
          }
          SASSERT(remaining_interpreted_tail.size() == ft_len - ut_len);
        }

        do_join_project(pt_len, head_pred, pos_tail_var_indexes, dealloc, m, pos_tail_preds, pos_tail_regs, remaining_negated_tail, remaining_interpreted_tail, ctx);

        TRACE("dl_stats", tout << "after join " << (ctx.reg(pos_tail_regs[0]) ? ctx.reg(pos_tail_regs[0])->get_size_estimate_rows() : 0) << "\n";);

        // clean up tmp regs for negation/filter before join
        int_set::iterator tr_it = tmp_regs.begin(), tr_end = tmp_regs.end();
        for (; tr_it != tr_end; ++tr_it) {
          g_compiler->make_dealloc_non_void(*tr_it, acc);
        }


        do_remaining_negation(remaining_negated_tail, head_pred, pos_tail_var_indexes, dealloc, m, pos_tail_preds, pos_tail_regs, ctx);

        do_remaining_filter(remaining_interpreted_tail, head_pred, pos_tail_var_indexes, dealloc, m, pos_tail_preds, pos_tail_regs, ctx);


        do_assemble(head_len, h, head_pred, pos_tail_var_indexes, dealloc, m, pos_tail_preds, pos_tail_regs, ctx);

        //    finish:
        g_compiler->m_instruction_observer.finish_rule();
        
        TRACE("dl", tout << "non-cache CODE\n"; acc.display(ctx, tout););
        acc.perform(ctx);

        return true;
      }
      virtual void display_head_impl(execution_context const& ctx, std::ostream & out) const {
        out << "exec ";
      }
      virtual void make_annotations(execution_context & ctx) {

      }
    };

    instruction * instruction::mk_exec(rule * r, reg_idx head_reg, const reg_idx * tail_regs,
      reg_idx delta_reg, bool use_widening) {
      return alloc(instr_exec, r, head_reg, tail_regs, delta_reg, use_widening);
    }


    // -----------------------------------
    //
    // instruction_block
    //
    // -----------------------------------

    instruction_block::~instruction_block() {
        reset();
    }

    void instruction_block::reset() {
        instr_seq_type::iterator it = m_data.begin();
        instr_seq_type::iterator end = m_data.end();
        for(; it!=end; ++it) {
            dealloc(*it);
        }
        m_data.reset();
        m_observer = 0;
    }

    bool instruction_block::perform(execution_context & ctx) const {
        cost_recorder crec;
        instr_seq_type::const_iterator it = m_data.begin();
        instr_seq_type::const_iterator end = m_data.end();
        bool success = true;
        for(; it!=end && success; ++it) {

            instruction * instr=(*it);
            crec.start(instr); //finish is performed by the next start() or by the destructor of crec

            TRACE("dl",      
                tout <<"% ";
                  instr->display_head_impl(ctx, tout);
                tout <<"\n";);
            success = !ctx.should_terminate() && instr->perform(ctx);
        }
        return success;
    }

    void instruction_block::process_all_costs() {
        instr_seq_type::iterator it = m_data.begin();
        instr_seq_type::iterator end = m_data.end();
        for(; it!=end; ++it) {
            (*it)->process_all_costs();
        }
    }


    void instruction_block::collect_statistics(statistics& st) const {
        instr_seq_type::const_iterator it = m_data.begin();
        instr_seq_type::const_iterator end = m_data.end();
        for(; it!=end; ++it) {
            (*it)->collect_statistics(st);
        }
    }

    void instruction_block::make_annotations(execution_context & ctx) {
        instr_seq_type::iterator it = m_data.begin();
        instr_seq_type::iterator end = m_data.end();
        for(; it!=end; ++it) {
            (*it)->make_annotations(ctx);
        }
    }

    void instruction_block::display_indented(execution_context const& _ctx, std::ostream & out, std::string indentation) const {
        rel_context const& ctx = _ctx.get_rel_context();
        instr_seq_type::const_iterator it = m_data.begin();
        instr_seq_type::const_iterator end = m_data.end();
        for(; it!=end; ++it) {
            instruction * i = (*it);
            if (i->passes_output_thresholds(ctx.get_context()) || i->being_recorded()) {
                i->display_indented(_ctx, out, indentation);
            }
        }
    }
}

