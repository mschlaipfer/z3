/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_compiler.cpp

Abstract:

    <abstract>

Author:

    Krystof Hoder (t-khoder) 2010-09-14.

Revision History:

--*/


#include <sstream>
#include"ref_vector.h"
#include"dl_context.h"
#include"rel_context.h"
#include"dl_rule.h"
#include"dl_util.h"
#include"dl_compiler.h"
#include"ast_pp.h"
#include"ast_smt2_pp.h"
#include<algorithm>


namespace datalog {

    void compiler::reset() {
        m_pred_regs.reset();
    }

    void compiler::ensure_predicate_loaded(func_decl * pred, execution_context & ctx) {
        pred2idx::obj_map_entry * e = m_pred_regs.insert_if_not_there2(pred, UINT_MAX);
        if (e->get_data().m_value != UINT_MAX) {
            //predicate is already loaded
            return;
        }
        relation_signature sig;
        m_context.get_rel_context()->get_rmanager().from_predicate(pred, sig);
        reg_idx reg = get_fresh_register(sig);
        e->get_data().m_value=reg;

        instruction::mk_load(m_context.get_manager(), pred, reg, ctx);
    }

    void compiler::make_join(bool empty, reg_idx t1, reg_idx t2, const variable_intersection & vars, reg_idx & result, 
        bool reuse_t1, execution_context & ctx) {
        relation_signature res_sig;
        relation_signature::from_join(m_reg_signatures[t1], m_reg_signatures[t2], vars.size(), 
            vars.get_cols1(), vars.get_cols2(), res_sig);
        result = get_register(res_sig, reuse_t1, t1);
        if (!empty) {
            instruction::mk_join(t1, t2, vars.size(), vars.get_cols1(), vars.get_cols2(), result, ctx);
        }
    }

    void compiler::make_join_project(bool empty, reg_idx t1, reg_idx t2, const variable_intersection & vars,
        const unsigned_vector & removed_cols, reg_idx & result, bool reuse_t1, execution_context & ctx) {
        relation_signature aux_sig;
        relation_signature sig1 = m_reg_signatures[t1];
        relation_signature sig2 = m_reg_signatures[t2];
        relation_signature::from_join(sig1, sig2, vars.size(), vars.get_cols1(), vars.get_cols2(), aux_sig);
        relation_signature res_sig;
        relation_signature::from_project(aux_sig, removed_cols.size(), removed_cols.c_ptr(), 
            res_sig);
        result = get_register(res_sig, reuse_t1, t1);

        if (!empty) {
            instruction::mk_join_project(t1, t2, vars.size(), vars.get_cols1(),
                vars.get_cols2(), removed_cols.size(), removed_cols.c_ptr(), result, ctx);
        }
    }

    void compiler::make_filter_interpreted_and_project(reg_idx src, app_ref & cond,
            const unsigned_vector & removed_cols, reg_idx & result, bool reuse, execution_context & ctx) {
        SASSERT(!removed_cols.empty());
        relation_signature res_sig;
        relation_signature::from_project(m_reg_signatures[src], removed_cols.size(),
            removed_cols.c_ptr(), res_sig);
        result = get_register(res_sig, reuse, src);

        instruction::mk_filter_interpreted_and_project(src, cond,
            removed_cols.size(), removed_cols.c_ptr(), result, ctx);
    }

    void compiler::make_select_equal_and_project(reg_idx src, const relation_element val, unsigned col,
        reg_idx & result, bool reuse, execution_context & ctx) {
        relation_signature res_sig;
        relation_signature::from_project(m_reg_signatures[src], 1, &col, res_sig);
        result = get_register(res_sig, reuse, src);
        instruction::mk_select_equal_and_project(m_context.get_manager(),
            src, val, col, result, ctx);
    }

    void compiler::make_clone(reg_idx src, reg_idx & result, execution_context & ctx) {
        relation_signature sig = m_reg_signatures[src];
        result = get_fresh_register(sig);
        
        instruction::mk_clone(src, result, ctx);
    }

    void compiler::make_union(reg_idx src, reg_idx tgt, reg_idx delta, bool use_widening, 
        execution_context & ctx) {
        SASSERT(m_reg_signatures[src] == m_reg_signatures[tgt]);
        SASSERT(delta == execution_context::void_register || m_reg_signatures[src] == m_reg_signatures[delta]);

        if (use_widening) {
            instruction::mk_widen(src, tgt, delta, ctx);
        }
        else {
            instruction::mk_union(src, tgt, delta, ctx);
        }
    }

    void compiler::make_projection(reg_idx src, unsigned col_cnt, const unsigned * removed_cols, 
        reg_idx & result, bool reuse, execution_context & ctx) {
        SASSERT(col_cnt > 0);

        relation_signature res_sig;
        relation_signature::from_project(m_reg_signatures[src], col_cnt, removed_cols, res_sig);
        result = get_register(res_sig, reuse, src);
        instruction::mk_projection(src, col_cnt, removed_cols, result, ctx);
    }

    compiler::reg_idx compiler::get_fresh_register(const relation_signature & sig) {
        //since we might be resizing the m_reg_signatures vector, the argument must not point inside it
        SASSERT((&sig>=m_reg_signatures.end()) || (&sig<m_reg_signatures.begin()));
        reg_idx result = m_reg_signatures.size();
        m_reg_signatures.push_back(sig);
        return result;
    }

    compiler::reg_idx compiler::get_register(const relation_signature & sig, bool reuse, compiler::reg_idx r) {
        if (!reuse) {
            return get_fresh_register(sig);
        }
        SASSERT(r != execution_context::void_register);
        m_reg_signatures[r] = sig;
        return r;
    }

    compiler::reg_idx compiler::get_single_column_register(const relation_sort s) {
        relation_signature singl_sig;
        singl_sig.push_back(s);
        return get_fresh_register(singl_sig);
    }

    void compiler::get_fresh_registers(const func_decl_set & preds,  pred2idx & regs) {
        func_decl_set::iterator pit = preds.begin();
        func_decl_set::iterator pend = preds.end();
        for(; pit != pend; ++pit) {
            func_decl * pred = *pit;
            reg_idx reg = m_pred_regs.find(pred);

            SASSERT(!regs.contains(pred));
            relation_signature sig = m_reg_signatures[reg];
            reg_idx delta_reg = get_fresh_register(sig);
            regs.insert(pred, delta_reg);
        }
    }

    void compiler::make_dealloc_non_void(reg_idx r, execution_context & ctx) {
        if (r != execution_context::void_register) {
            // m_reg_signatures does not get updated
            instruction::mk_dealloc(r, ctx);
        }
    }

    void compiler::make_add_constant_column(func_decl* head_pred, reg_idx src, const relation_sort s, const relation_element val,
        reg_idx & result, bool & dealloc, execution_context & ctx) {
        reg_idx singleton_table;
        if (!m_constant_registers.find(s, val, singleton_table)) {
            singleton_table = get_single_column_register(s);
            instruction::mk_unary_singleton(m_context.get_manager(), head_pred, s, val, singleton_table, ctx);
            m_constant_registers.insert(s, val, singleton_table);
        }
        if (src == execution_context::void_register) {
            result = singleton_table;
            SASSERT(dealloc == false);
        }
        else {
            variable_intersection empty_vars(m_context.get_manager());
            make_join(false, src, singleton_table, empty_vars, result, dealloc, ctx);
            dealloc = true;
        }
    }

    void compiler::make_add_unbound_column(rule* compiled_rule, unsigned col_idx, func_decl* pred, reg_idx src, const relation_sort s, reg_idx & result,
        bool & dealloc, execution_context & ctx) {
        
        TRACE("dl", tout << "Adding unbound column " << mk_pp(pred, m_context.get_manager()) << "\n";);
            IF_VERBOSE(3, { 
                    expr_ref e(m_context.get_manager()); 
                    m_context.get_rule_manager().to_formula(*compiled_rule, e); 
                    verbose_stream() << "Compiling unsafe rule column " << col_idx << "\n" 
                                     << mk_ismt2_pp(e, m_context.get_manager()) << "\n"; 
                });
        reg_idx total_table;
        if (!m_total_registers.find(s, pred, total_table)) {
            total_table = get_single_column_register(s);
            relation_signature sig;
            sig.push_back(s);
            instruction::mk_total(sig, pred, total_table, ctx);
            m_total_registers.insert(s, pred, total_table);
        }       
        if (src == execution_context::void_register) {
            result = total_table;
            SASSERT(dealloc == false);
        }
        else {
            variable_intersection empty_vars(m_context.get_manager());
            make_join(false, src, total_table, empty_vars, result, dealloc, ctx);
            dealloc = true;
        }
    }

    void compiler::make_full_relation(func_decl* pred, const relation_signature & sig, reg_idx & result, 
        execution_context & ctx) {
        SASSERT(sig.empty());
        TRACE("dl", tout << "Adding unbound column " << mk_pp(pred, m_context.get_manager()) << "\n";);
        if (m_empty_tables_registers.find(pred, result)) {
            return;
        }

        result = get_fresh_register(sig);
        instruction::mk_total(sig, pred, result, ctx);
        m_empty_tables_registers.insert(pred, result);
    }


    void compiler::make_duplicate_column(reg_idx src, unsigned col, reg_idx & result, 
        bool reuse, execution_context & ctx) {

        relation_signature & src_sig = m_reg_signatures[src];
        reg_idx single_col_reg;
        unsigned src_col_cnt = src_sig.size();
        if(src_col_cnt == 1) {
            single_col_reg = src;
        }
        else {
            unsigned_vector removed_cols;
            for(unsigned i=0; i<src_col_cnt; i++) {
                if(i != col) {
                    removed_cols.push_back(i);
                }
            }
            make_projection(src, removed_cols.size(), removed_cols.c_ptr(), single_col_reg, false, ctx);
        }
        variable_intersection vi(m_context.get_manager());
        vi.add_pair(col, 0);
        make_join(false, src, single_col_reg, vi, result, reuse, ctx);
        if (src_col_cnt != 1) {
            make_dealloc_non_void(single_col_reg, ctx);
        }
    }

    void compiler::make_rename(reg_idx src, unsigned cycle_len, const unsigned * permutation_cycle, 
        reg_idx & result, bool reuse, execution_context & ctx) {
        relation_signature res_sig;
        relation_signature::from_rename(m_reg_signatures[src], cycle_len, permutation_cycle, res_sig);
        result = get_register(res_sig, reuse, src);
        instruction::mk_rename(src, cycle_len, permutation_cycle, result, ctx);
    }

    void compiler::make_assembling_code(
        rule* compiled_rule, 
        func_decl* head_pred, 
        reg_idx    src, 
        const svector<assembling_column_info> & acis0,
        reg_idx &           result, 
        bool & dealloc,
        execution_context & ctx) {

        TRACE("dl", tout << mk_pp(head_pred, m_context.get_manager()) << "\n";);

        unsigned col_cnt = acis0.size();
        reg_idx curr = src;

        relation_signature empty_signature;

        relation_signature * curr_sig;
        if (curr != execution_context::void_register) {
            curr_sig = & m_reg_signatures[curr];
        }
        else {
            curr_sig = & empty_signature;
        }
        unsigned src_col_cnt = curr_sig->size();

        svector<assembling_column_info> acis(acis0);
        int2int handled_unbound;

        //first remove unused source columns
        int_set referenced_src_cols;
        for (unsigned i = 0; i < col_cnt; i++) {
            if (acis[i].kind == ACK_BOUND_VAR) {
                SASSERT(acis[i].source_column < src_col_cnt); //we refer only to existing columns
                referenced_src_cols.insert(acis[i].source_column);
            }
        }

        //if an ACK_BOUND_VAR pointed to column i, after projection it will point to
        //i-new_src_col_offset[i] due to removal of some of earlier columns
        unsigned_vector new_src_col_offset;

        unsigned_vector src_cols_to_remove;
        for (unsigned i = 0; i < src_col_cnt; i++) {
            if(!referenced_src_cols.contains(i)) {
                src_cols_to_remove.push_back(i);
            }
            new_src_col_offset.push_back(src_cols_to_remove.size());
        }
        if (!src_cols_to_remove.empty()) {
            make_projection(curr, src_cols_to_remove.size(), src_cols_to_remove.c_ptr(), curr, dealloc, ctx);
            dealloc = true;
            curr_sig = & m_reg_signatures[curr];

            //update ACK_BOUND_VAR references
            for (unsigned i = 0; i < col_cnt; i++) {
                if (acis[i].kind == ACK_BOUND_VAR) {
                    unsigned col = acis[i].source_column;
                    acis[i].source_column = col-new_src_col_offset[col];
                }
            }
        }

        //convert all result columns into bound variables by extending the source table
        for (unsigned i = 0; i < col_cnt; i++) {
            if (acis[i].kind == ACK_BOUND_VAR) {
                continue;
            }
            unsigned bound_column_index;
            if (acis[i].kind != ACK_UNBOUND_VAR || !handled_unbound.find(acis[i].var_index,bound_column_index)) {
                bound_column_index = curr_sig->size();
                if(acis[i].kind == ACK_CONSTANT) {
                    make_add_constant_column(head_pred, curr, acis[i].domain, acis[i].constant, curr, dealloc, ctx);
                }
                else {
                    SASSERT(acis[i].kind == ACK_UNBOUND_VAR);
                    make_add_unbound_column(compiled_rule, i, head_pred, curr, acis[i].domain, curr, dealloc, ctx);
                    handled_unbound.insert(acis[i].var_index,bound_column_index);
                }
                curr_sig = & m_reg_signatures[curr];
                SASSERT(bound_column_index==curr_sig->size()-1);
            }
            SASSERT((*curr_sig)[bound_column_index] == acis[i].domain);
            acis[i].kind = ACK_BOUND_VAR;
            acis[i].source_column = bound_column_index;
        }

        //duplicate needed source columns
        int_set used_cols;
        for (unsigned i = 0; i < col_cnt; i++) {
            SASSERT(acis[i].kind == ACK_BOUND_VAR);
            unsigned col = acis[i].source_column;
            if(!used_cols.contains(col)) {
                used_cols.insert(col);
                continue;
            }
            make_duplicate_column(curr, col, curr, dealloc, ctx);
            dealloc = true;
            curr_sig = & m_reg_signatures[curr];
            unsigned bound_column_index = curr_sig->size()-1;
            SASSERT((*curr_sig)[bound_column_index] == acis[i].domain);
            acis[i].source_column=bound_column_index;
        }

        //reorder source columns to match target
        SASSERT(curr_sig->size() == col_cnt); //now the intermediate table is a permutation
        for (unsigned i = 0; i < col_cnt; i++) {
            if (acis[i].source_column==i) {
                continue;
            }
            unsigned_vector permutation;
            unsigned next = i;
            do {
                permutation.push_back(next);
                unsigned prev = next;
                next=acis[prev].source_column;
                SASSERT(next >= i); //columns below i are already reordered
                SASSERT(next < col_cnt);
                acis[prev].source_column = prev;
                SASSERT(permutation.size() <= col_cnt); //this should not be an infinite loop
            } while (next != i);

            make_rename(curr, permutation.size(), permutation.c_ptr(), curr, dealloc, ctx);
            dealloc = true;
            curr_sig = & m_reg_signatures[curr];
        }

        if (curr == execution_context::void_register) {
            SASSERT(src == execution_context::void_register);
            SASSERT(acis0.size() == 0);
            make_full_relation(head_pred, empty_signature, curr, ctx);
            dealloc = false;
        }

        result = curr;
    }
    
    void compiler::add_unbound_columns_for_negation(rule* r, func_decl* pred, reg_idx& single_res, expr_ref_vector& single_res_expr,
      int2ints & var_indexes,
      bool & dealloc, execution_context & ctx) {
        uint_set pos_vars;
        u_map<expr*> neg_vars;
        ast_manager& m = m_context.get_manager();
        unsigned pt_len = r->get_positive_tail_size();
        unsigned ut_len = r->get_uninterpreted_tail_size();

        // no negated predicates
        if (pt_len == ut_len)
            return;

        // populate negative variables:
        for (unsigned i = pt_len; i < ut_len; ++i) {
        #if 0
            if (!apply_now.contains(i))
                continue;
        #endif
            app * neg_tail = r->get_tail(i);
            unsigned neg_len = neg_tail->get_num_args();
            for (unsigned j = 0; j < neg_len; ++j) {
                expr * e = neg_tail->get_arg(j);
                if (is_var(e)) {
                    unsigned idx = to_var(e)->get_idx();
                    neg_vars.insert(idx, e);
                }
            }
        }
        // populate positive variables:
        for (unsigned i = 0; i < single_res_expr.size(); ++i) {
            expr* e = single_res_expr[i].get();
            if (is_var(e)) {
                pos_vars.insert(to_var(e)->get_idx());
            }
        }
        // add negative variables that are not in positive
        u_map<expr*>::iterator it = neg_vars.begin(), end = neg_vars.end();
        for (; it != end; ++it) {
            unsigned v = it->m_key;
            expr* e = it->m_value;
            if (!pos_vars.contains(v)) {
                single_res_expr.push_back(e);

                int2ints::entry * entry = var_indexes.insert_if_not_there2(v, unsigned_vector());
                entry->get_data().m_value.push_back(single_res_expr.size() - 1);

                make_add_unbound_column(r, v, pred, single_res, m.get_sort(e), single_res, dealloc, ctx);
                TRACE("dl", tout << "Adding unbound column: " << mk_pp(e, m) << "\n";);
            }
        }
    }

    void compiler::compile_rule_evaluation(rule * r, const pred2idx * input_deltas,
        reg_idx output_delta, bool use_widening, execution_context & ctx) {
        typedef std::pair<reg_idx, unsigned> tail_delta_info; //(delta register, tail index)
        typedef svector<tail_delta_info> tail_delta_infos;

        unsigned rule_len = r->get_uninterpreted_tail_size();
        reg_idx head_reg = m_pred_regs.find(r->get_decl());

        svector<reg_idx> tail_regs;
        tail_delta_infos tail_deltas;
        for (unsigned j = 0; j < rule_len; j++) {
            func_decl * tail_pred = r->get_tail(j)->get_decl();
            reg_idx tail_reg = m_pred_regs.find(tail_pred);
            tail_regs.push_back(tail_reg);

            if (input_deltas && !all_or_nothing_deltas()) {
                reg_idx tail_delta_idx;
                if (input_deltas->find(tail_pred, tail_delta_idx)) {
                    tail_deltas.push_back(tail_delta_info(tail_delta_idx, j));
                }
            }
        }

        if(!input_deltas || all_or_nothing_deltas()) {
            instruction::mk_exec(r, head_reg, tail_regs.c_ptr(), output_delta, use_widening, ctx);
        }
        else {
            tail_delta_infos::iterator tdit = tail_deltas.begin();
            tail_delta_infos::iterator tdend = tail_deltas.end();
            for (; tdit != tdend; ++tdit) {
                tail_delta_info tdinfo = *tdit;
                flet<reg_idx> flet_tail_reg(tail_regs[tdinfo.second], tdinfo.first);
                instruction::mk_exec(r, head_reg, tail_regs.c_ptr(), output_delta, use_widening, ctx);
            }
        }
    }

    class cycle_breaker
    {
        typedef func_decl * T;
        typedef rule_dependencies::item_set item_set; //set of T

        rule_dependencies & m_deps;
        item_set & m_removed;
        svector<T> m_stack;
        ast_mark m_stack_content;
        ast_mark m_visited;

        void traverse(T v) {
            SASSERT(!m_stack_content.is_marked(v)); 
            if(m_visited.is_marked(v) || m_removed.contains(v)) { 
                return;
            }

            m_stack.push_back(v);
            m_stack_content.mark(v, true); 
            m_visited.mark(v, true);

            const item_set & deps = m_deps.get_deps(v);
            item_set::iterator it = deps.begin();
            item_set::iterator end = deps.end();
            for (; it != end; ++it) {
                T d = *it;
                if (m_stack_content.is_marked(d)) { 
                    //TODO: find the best vertex to remove in the cycle
                    m_removed.insert(v);
                    break;
                }
                traverse(d);
            }
            SASSERT(m_stack.back()==v);

            m_stack.pop_back();
            m_stack_content.mark(v, false); 
        }

    public:
        cycle_breaker(rule_dependencies & deps, item_set & removed) 
            : m_deps(deps), m_removed(removed) { SASSERT(removed.empty()); }

        void operator()() {
            rule_dependencies::iterator it = m_deps.begin();
            rule_dependencies::iterator end = m_deps.end();
            for (; it != end; ++it) {
                T v = it->m_key;
                traverse(v);
            }
            m_deps.remove(m_removed);
        }
    };

    void compiler::detect_chains(const func_decl_set & preds, func_decl_vector & ordered_preds, 
            func_decl_set & global_deltas) {

        SASSERT(ordered_preds.empty());
        SASSERT(global_deltas.empty());

        rule_dependencies deps(m_rule_set.get_dependencies());
        deps.restrict(preds);
        cycle_breaker(deps, global_deltas)();
        VERIFY( deps.sort_deps(ordered_preds) );

        //the predicates that were removed to get acyclic induced subgraph are put last
        //so that all their local input deltas are already populated
        func_decl_set::iterator gdit = global_deltas.begin();
        func_decl_set::iterator gend = global_deltas.end();
        for (; gdit != gend; ++gdit) {
            ordered_preds.push_back(*gdit);
        }
    }

    void compiler::compile_preds(const func_decl_vector & head_preds, const func_decl_set & widened_preds,
        const pred2idx * input_deltas, const pred2idx & output_deltas, execution_context & ctx) {
        func_decl_vector::const_iterator hpit = head_preds.begin();
        func_decl_vector::const_iterator hpend = head_preds.end();
        for (; hpit!=hpend; ++hpit) {
            func_decl * head_pred = *hpit;

            bool widen_predicate_in_loop = widened_preds.contains(head_pred);

            reg_idx d_head_reg; //output delta for the initial rule execution
            if (!output_deltas.find(head_pred, d_head_reg)) {
                d_head_reg = execution_context::void_register;
            }

            const rule_vector & pred_rules = m_rule_set.get_predicate_rules(head_pred);
            rule_vector::const_iterator rit = pred_rules.begin();
            rule_vector::const_iterator rend = pred_rules.end();
            for(; rit!=rend; ++rit) {
                rule * r = *rit;
                SASSERT(head_pred==r->get_decl());

                compile_rule_evaluation(r, input_deltas, d_head_reg, widen_predicate_in_loop, ctx);
            }
        }
    }

    void compiler::compile_preds_init(const func_decl_vector & head_preds, const func_decl_set & widened_preds,
      const pred2idx * input_deltas, const pred2idx & output_deltas, execution_context & ctx) {
        func_decl_vector::const_iterator hpit = head_preds.begin();
        func_decl_vector::const_iterator hpend = head_preds.end();
        reg_idx void_reg = execution_context::void_register;
        for (; hpit != hpend; ++hpit) {
            func_decl * head_pred = *hpit;
            const rule_vector & pred_rules = m_rule_set.get_predicate_rules(head_pred);
            rule_vector::const_iterator rit = pred_rules.begin();
            rule_vector::const_iterator rend = pred_rules.end();
            unsigned stratum = m_rule_set.get_predicate_strat(head_pred);

            for (; rit != rend; ++rit) {
                rule * r = *rit;
                SASSERT(head_pred==r->get_decl());

                for (unsigned i = 0; i < r->get_uninterpreted_tail_size(); ++i) {
                    unsigned stratum1 = m_rule_set.get_predicate_strat(r->get_decl(i));
                    if (stratum1 >= stratum) {
                        goto next_loop;
                    }
                }
                compile_rule_evaluation(r, input_deltas, void_reg, false, ctx);
            next_loop:
                ;
            }

            reg_idx d_head_reg;
            if (output_deltas.find(head_pred, d_head_reg)) {
                instruction::mk_clone(m_pred_regs.find(head_pred), d_head_reg, ctx);
            }
        }
    }

    void compiler::make_inloop_delta_transition(const pred2idx & global_head_deltas, 
        const pred2idx & global_tail_deltas, const pred2idx & local_deltas, execution_context & ctx) {
        //move global head deltas into tail ones
        pred2idx::iterator gdit = global_head_deltas.begin();
        pred2idx::iterator gend = global_head_deltas.end();
        for(; gdit!=gend; ++gdit) {
            func_decl * pred = gdit->m_key;
            reg_idx head_reg = gdit->m_value;
            reg_idx tail_reg = global_tail_deltas.find(pred);
            instruction::mk_move(head_reg, tail_reg, ctx);
        }
        //empty local deltas
        pred2idx::iterator lit = local_deltas.begin();
        pred2idx::iterator lend = local_deltas.end();
        for (; lit!=lend; ++lit) {
            instruction::mk_dealloc(lit->m_value, ctx);
        }
    }

    bool compiler::control_is_empty(const svector<reg_idx> & controls, execution_context & ctx) {
        svector<reg_idx>::const_iterator it = controls.begin();
        svector<reg_idx>::const_iterator end = controls.end();
        for (; it != end; ++it) {
            reg_idx r = *it;
            if (ctx.reg(r) && !ctx.reg(r)->fast_empty()) {
                return false;
            }
        }
        return true;
    }

    void compiler::compile_loop(const func_decl_vector & head_preds, const func_decl_set & widened_preds,
            const pred2idx & global_head_deltas, const pred2idx & global_tail_deltas, 
            const pred2idx & local_deltas, execution_context & ctx) {

        pred2idx all_head_deltas(global_head_deltas);
        unite_disjoint_maps(all_head_deltas, local_deltas);
        pred2idx all_tail_deltas(global_tail_deltas);
        unite_disjoint_maps(all_tail_deltas, local_deltas);

        svector<reg_idx> loop_control_regs; //loop is controlled by global src regs
        collect_map_range(loop_control_regs, global_tail_deltas);
        // TODO: Maybe model early loop exit, but currently none of the instructions returns false anyhow,
        //       so this is not relevant at the moment.
        while (!control_is_empty(loop_control_regs, ctx)) {
            //generate code for the iterative fixpoint search
            //The order in which we iterate the preds_vector matters, since rules can depend on
            //deltas generated earlier in the same iteration.
            compile_preds(head_preds, widened_preds, &all_tail_deltas, all_head_deltas, ctx);

            //move target deltas into source deltas at the end of the loop
            //and clear local deltas
            make_inloop_delta_transition(global_head_deltas, global_tail_deltas, local_deltas, ctx);
        }
    }

    void compiler::compile_dependent_rules(const func_decl_set & head_preds,
            const pred2idx * input_deltas, const pred2idx & output_deltas, 
            bool add_saturation_marks, execution_context & ctx) {
        
        if (!output_deltas.empty()) {
            func_decl_set::iterator hpit = head_preds.begin();
            func_decl_set::iterator hpend = head_preds.end();
            for(; hpit!=hpend; ++hpit) {
                if(output_deltas.contains(*hpit)) {
                    //we do not support retrieving deltas for rules that are inside a recursive 
                    //stratum, since we would have to maintain this 'global' delta through the loop
                    //iterations
                    NOT_IMPLEMENTED_YET();
                }
            }
        }

        func_decl_vector preds_vector;
        func_decl_set global_deltas_dummy;

        detect_chains(head_preds, preds_vector, global_deltas_dummy);

        /*
          FIXME: right now we use all preds as global deltas for correctness purposes
        func_decl_set local_deltas(head_preds);
        set_difference(local_deltas, global_deltas);
        */
        func_decl_set local_deltas;
        func_decl_set global_deltas(head_preds);

        pred2idx d_global_src;  //these deltas serve as sources of tuples for rule evaluation inside the loop
        get_fresh_registers(global_deltas, d_global_src);
        pred2idx d_global_tgt;  //these deltas are targets for new tuples in rule evaluation inside the loop
        get_fresh_registers(global_deltas, d_global_tgt);
        pred2idx d_local;
        get_fresh_registers(local_deltas, d_local);

        pred2idx d_all_src(d_global_src); //src together with local deltas
        unite_disjoint_maps(d_all_src, d_local);
        pred2idx d_all_tgt(d_global_tgt); //tgt together with local deltas
        unite_disjoint_maps(d_all_tgt, d_local);


        func_decl_set empty_func_decl_set;

        //generate code for the initial run
        // compile_preds(preds_vector, empty_func_decl_set, input_deltas, d_global_src, acc);
        compile_preds_init(preds_vector, empty_func_decl_set, input_deltas, d_global_src, ctx);

        if (compile_with_widening()) {
            compile_loop(preds_vector, global_deltas, d_global_tgt, d_global_src, d_local, ctx);
        }
        else {
            compile_loop(preds_vector, empty_func_decl_set, d_global_tgt, d_global_src, d_local, ctx);
        }


        if (add_saturation_marks) {
            //after the loop finishes, all predicates in the group are saturated, 
            //so we may mark them as such
            func_decl_set::iterator fdit = head_preds.begin();
            func_decl_set::iterator fdend = head_preds.end();
            for (; fdit!=fdend; ++fdit) {
                instruction::mk_mark_saturated(m_context.get_manager(), *fdit, ctx);
            }
        }
    }

    bool compiler::is_nonrecursive_stratum(const func_decl_set & preds) const {
        SASSERT(preds.size()>0);
        if (preds.size()>1) {
            return false;
        }
        func_decl * head_pred = *preds.begin();
        const rule_vector & rules = m_rule_set.get_predicate_rules(head_pred);
        rule_vector::const_iterator it = rules.begin();
        rule_vector::const_iterator end = rules.end();
        for (; it!=end; ++it) {
            //it is sufficient to check just for presence of the first head predicate,
            //since if the rules are recursive and their heads are strongly connected by dependence,
            //this predicate must appear in some tail
            if ((*it)->is_in_tail(head_pred)) {
                return false;
            }
        }
        return true;
    }

    void compiler::compile_nonrecursive_stratum(const func_decl_set & preds, 
            const pred2idx * input_deltas, const pred2idx & output_deltas, 
            bool add_saturation_marks, execution_context & ctx) {
        //non-recursive stratum always has just one head predicate
        SASSERT(preds.size()==1);
        SASSERT(is_nonrecursive_stratum(preds));
        func_decl * head_pred = *preds.begin();
        const rule_vector & rules = m_rule_set.get_predicate_rules(head_pred);



        reg_idx output_delta;
        if (!output_deltas.find(head_pred, output_delta)) {
            output_delta = execution_context::void_register;
        }

        rule_vector::const_iterator it = rules.begin();
        rule_vector::const_iterator end = rules.end();
        for (; it != end; ++it) {
            rule * r = *it;
            SASSERT(r->get_decl()==head_pred);

            compile_rule_evaluation(r, input_deltas, output_delta, false, ctx);
        }

        if (add_saturation_marks) {
            //now the predicate is saturated, so we may mark it as such
            instruction::mk_mark_saturated(m_context.get_manager(), head_pred, ctx);
        }
    }

    bool compiler::all_saturated(const func_decl_set & preds) const {
        func_decl_set::iterator fdit = preds.begin();
        func_decl_set::iterator fdend = preds.end();
        for (; fdit != fdend; ++fdit) {
            if (!m_context.get_rel_context()->get_rmanager().is_saturated(*fdit)) {
                return false;
            }
        }
        return true;
    }

    void compiler::compile_strats(const rule_stratifier & stratifier, 
            const pred2idx * input_deltas, const pred2idx & output_deltas, 
            bool add_saturation_marks, execution_context & ctx) {
        rule_set::pred_set_vector strats = stratifier.get_strats();
        rule_set::pred_set_vector::const_iterator sit = strats.begin();
        rule_set::pred_set_vector::const_iterator send = strats.end();
        for (; sit!=send; ++sit) {
            func_decl_set & strat_preds = **sit;

            if (all_saturated(strat_preds)) {
                //all predicates in stratum are saturated, so no need to compile rules for them
                continue;
            }

            TRACE("dl",
                tout << "Stratum: ";
                func_decl_set::iterator pit = strat_preds.begin();
                func_decl_set::iterator pend = strat_preds.end();
                for(; pit!=pend; ++pit) {
                    func_decl * pred = *pit;
                    tout << pred->get_name() << " ";
                }
                tout << "\n";
                );

            if (is_nonrecursive_stratum(strat_preds)) {
                //this stratum contains just a single non-recursive rule
                compile_nonrecursive_stratum(strat_preds, input_deltas, output_deltas, add_saturation_marks, ctx);
            }
            else {
                compile_dependent_rules(strat_preds, input_deltas, output_deltas, 
                    add_saturation_marks, ctx);
            }
        }
    }

    void compiler::do_compilation(execution_context & ectx) {

        unsigned rule_cnt=m_rule_set.get_num_rules();
        if (rule_cnt == 0) {
            return;
        }

        //load predicate data
        for(unsigned i = 0; i < rule_cnt; i++) {
            const rule * r = m_rule_set.get_rule(i);
            ensure_predicate_loaded(r->get_decl(), ectx);

            unsigned rule_len = r->get_uninterpreted_tail_size();
            for(unsigned j = 0; j < rule_len; j++) {
                ensure_predicate_loaded(r->get_tail(j)->get_decl(), ectx);
            }
        }
        
        pred2idx empty_pred2idx_map;

        compile_strats(m_rule_set.get_stratifier(), static_cast<pred2idx *>(0), 
            empty_pred2idx_map, true, ectx);



        //store predicate data
        pred2idx::iterator pit = m_pred_regs.begin();
        pred2idx::iterator pend = m_pred_regs.end();
        for (; pit != pend; ++pit) {
            pred2idx::key_data & e = *pit;
            func_decl * pred = e.m_key;
            reg_idx reg = e.m_value;
            instruction::mk_store(m_context.get_manager(), pred, reg, ectx);
        }
    }


}

