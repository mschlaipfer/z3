/*++
  Copyright (c) 2013 Microsoft Corporation

  Module Name:

  interpolant_cmds.cpp

  Abstract:
  Commands for interpolation.

  Author:

  Leonardo (leonardo) 2011-12-23

  Notes:

  --*/
#include<sstream>
#include"cmd_context.h"
#include"cmd_util.h"
#include"scoped_timer.h"
#include"scoped_ctrl_c.h"
#include"cancel_eh.h"
#include"ast_pp.h"
#include"ast_smt_pp.h"
#include"ast_smt2_pp.h"
#include"parametric_cmd.h"
#include"mpq.h"
#include"expr2var.h"
#include"pp.h"
#include"pp_params.hpp"
#include"iz3interp.h"
#include"iz3checker.h"
#include"iz3profiling.h"
#include"interp_params.hpp"
#include"scoped_proof.h"
#include"bv2lia_rewriter.h"
#include"lia2bv_rewriter.h"

static void show_interpolant_and_maybe_check(cmd_context & ctx,
                                             ptr_vector<ast> &cnsts,
                                             expr *t, 
                                             ptr_vector<ast> &interps,
                                             params_ref &m_params,
                                             bool check)
{
  
    if (m_params.get_bool("som", false))
        m_params.set_bool("flat", true);
    th_rewriter s(ctx.m(), m_params);
  
    for(unsigned i = 0; i < interps.size(); i++){

        expr_ref r(ctx.m());
        proof_ref pr(ctx.m());
        s(to_expr(interps[i]),r,pr);

        ctx.regular_stream()  << mk_pp(r.get(), ctx.m()) << std::endl;
#if 0
        ast_smt_pp pp(ctx.m());
        pp.set_logic(ctx.get_logic().str().c_str());
        pp.display_smt2(ctx.regular_stream(), to_expr(interps[i]));
        ctx.regular_stream() << std::endl;
#endif
    }

    s.cleanup();

    // verify, for the paranoid...
    if(check || interp_params(m_params).check()){
        std::ostringstream err;
        ast_manager &_m = ctx.m();

        // need a solver -- make one here FIXME is this right?
        bool proofs_enabled, models_enabled, unsat_core_enabled;
        params_ref p;
        ctx.params().get_solver_params(_m, p, proofs_enabled, models_enabled, unsat_core_enabled);
        scoped_ptr<solver> sp = (ctx.get_solver_factory())(_m, p, false, true, false, ctx.get_logic());

        if(iz3check(_m,sp.get(),err,cnsts,t,interps))
            ctx.regular_stream() << "correct\n";
        else 
            ctx.regular_stream() << "incorrect: " << err.str().c_str() << "\n";
    }

    for(unsigned i = 0; i < interps.size(); i++){
        ctx.m().dec_ref(interps[i]);
    }

    interp_params itp_params(m_params);
    if(itp_params.profile())
        profiling::print(ctx.regular_stream());

}

static void check_can_interpolate(cmd_context & ctx){
    if (!ctx.produce_interpolants())
        throw cmd_exception("interpolation is not enabled, use command (set-option :produce-interpolants true)");
}


static void get_interpolant_and_maybe_check(cmd_context & ctx, expr * t, params_ref &m_params, bool check) {

    check_can_interpolate(ctx);

    // get the proof, if there is one

    if (!ctx.has_manager() ||
        ctx.cs_state() != cmd_context::css_unsat)
        throw cmd_exception("proof is not available");
    expr_ref pr(ctx.m());
    pr = ctx.get_check_sat_result()->get_proof();
    if (pr == 0)
        throw cmd_exception("proof is not available");

    // get the assertions from the context

    ptr_vector<expr>::const_iterator it  = ctx.begin_assertions();
    ptr_vector<expr>::const_iterator end = ctx.end_assertions();
    ptr_vector<ast> cnsts((unsigned)(end - it));
    for (int i = 0; it != end; ++it, ++i)
        cnsts[i] = *it;
    
    // compute an interpolant
  
    ptr_vector<ast> interps;
 
    try {
        iz3interpolate(ctx.m(),pr.get(),cnsts,t,interps,0);
    }
    catch (iz3_bad_tree &) {
        throw cmd_exception("interpolation pattern contains non-asserted formula");
    }
    catch (iz3_incompleteness &) {
        throw cmd_exception("incompleteness in interpolator");
    }

    show_interpolant_and_maybe_check(ctx, cnsts, t, interps, m_params, check);
}

static void get_interpolant(cmd_context & ctx, expr * t, params_ref &m_params) {
    get_interpolant_and_maybe_check(ctx,t,m_params,false);
}

#if 0
static void get_and_check_interpolant(cmd_context & ctx, params_ref &m_params, expr * t) {
    get_interpolant_and_maybe_check(ctx,t,m_params,true);
}
#endif

static void compute_interpolant_and_maybe_check(cmd_context & ctx, expr * t, obj_map<expr, expr*> &beta, params_ref &m_params, bool check){
    
    // create a fresh solver suitable for interpolation
    bool proofs_enabled, models_enabled, unsat_core_enabled;
    params_ref p;
    ast_manager &_m = ctx.m();

    // TODO: the following is a HACK to enable proofs in the old smt solver
    // When we stop using that solver, this hack can be removed
    scoped_proof_mode spm(_m,PGM_FINE);
    ctx.params().get_solver_params(_m, p, proofs_enabled, models_enabled, unsat_core_enabled);
    p.set_bool("proof", true);
    scoped_ptr<solver> sp = (ctx.get_interpolating_solver_factory())(_m, p, true, models_enabled, false, ctx.get_logic());

    ptr_vector<ast> cnsts;
    ptr_vector<ast> interps, interps_rw;
    model_ref m;
  
    // compute an interpolant
  
    lbool res;
    try {
        res = iz3interpolate(_m, *sp.get(), t, cnsts, interps, m, 0);
        if (m_params.get_bool(":use-bv2lia", false)) {
            TRACE("lia2bv", tout << "rewrite LIA interpolant(s) to BV" << std::endl;);

            // TODO produce proofs?
            lia2bv_rewriter lia2bv_rw = lia2bv_rewriter(ctx.m(), m_params);

            lia2bv_rw.cfg().set_lia2bv(&beta);
            for(ptr_vector<ast>::iterator it = interps.begin(); it != interps.end(); ++it) {
                TRACE("lia2bv", tout << "interp it: " << mk_pp(*it, ctx.m()) << std::endl;);
                app *a = to_app(*it);
                expr_ref *res_itp = new expr_ref(ctx.m());
                lia2bv_rw(a, a->get_num_args(), a->get_args(), *res_itp);
                interps_rw.push_back(*res_itp);
                TRACE("lia2bv", tout << "bv itp candidate: " << mk_pp(*res_itp, ctx.m()) << std::endl;);
                //delete res_itp;
            }

        }
    }
    catch (iz3_incompleteness &) {
        throw cmd_exception("incompleteness in interpolator");
    }

    switch(res){
    case l_false:
        ctx.regular_stream() << "unsat\n";
        if (m_params.get_bool(":use-bv2lia", false)) {
            show_interpolant_and_maybe_check(ctx, cnsts, t, interps_rw, m_params, check);
            // TODO maybe find better spot for cleanup
            for(unsigned i = 0; i < interps.size(); i++){
                ctx.m().dec_ref(interps[i]);
            }
        } else {
            show_interpolant_and_maybe_check(ctx, cnsts, t, interps, m_params, check);
        }
        break;

    case l_true:
        ctx.regular_stream() << "sat\n";
        // TODO: how to return the model to the context, if it exists?
        break;

    case l_undef:
        ctx.regular_stream() << "unknown\n";
        // TODO: how to return the model to the context, if it exists?
        break;
    }    

    for(unsigned i = 0; i < cnsts.size(); i++)
        ctx.m().dec_ref(cnsts[i]);

}

static expr *make_tree(cmd_context & ctx, const ptr_vector<expr> &exprs){
    if(exprs.size() == 0)
        throw cmd_exception("not enough arguments");
    expr *foo = exprs[0];
    for(unsigned i = 1; i < exprs.size(); i++){
        expr* interp = ctx.m().mk_interp(foo);
        foo = ctx.m().mk_and(interp,exprs[i]);
    }    
    return foo;
}

static void get_interpolant(cmd_context & ctx, const ptr_vector<expr> &exprs, params_ref &m_params) {
    expr_ref foo(make_tree(ctx, exprs),ctx.m());
    get_interpolant(ctx,foo.get(),m_params);
}

static void compute_interpolant(cmd_context & ctx, const ptr_vector<expr> &exprs, params_ref &m_params) {
    if (m_params.get_bool(":use-bv2lia", false)) {
        TRACE("bv2lia", tout << "convert exprs before interpolating.\n";);
        bv2lia_rewriter bv2lia_rw = bv2lia_rewriter(ctx.m(), m_params);
        ptr_vector<expr_ref> tmp;
        ptr_vector<expr> lia_exprs;
        for (ptr_vector<expr>::const_iterator it = exprs.begin(); it != exprs.end(); ++it) {
            bv2lia_rw.reset();
            TRACE("bv2lia", tout << "before rewrite expr: " << mk_pp(*it, ctx.m()) << std::endl;);
            app *a = to_app(*it);
            // TODO can I get rid of the obvious allocation here?
            expr_ref *res = new expr_ref(ctx.m());
            bv2lia_rw(a, a->get_num_args(), a->get_args(), *res);
            tmp.push_back(res);

            expr_ref_vector lia_part(ctx.m());
            lia_part.append(bv2lia_rw.cfg().get_side_conditions());
            lia_part.push_back(*res);
            expr* lia_and = ctx.m().mk_and(lia_part.size(), lia_part.c_ptr());
            lia_exprs.push_back(lia_and);

            TRACE("bv2lia", tout << "after rewrite expr: " << mk_pp(*res, ctx.m()) << std::endl;);
            TRACE("bv2lia", tout << "with side conditions: " << mk_pp(lia_and, ctx.m()) << std::endl;);
        }

        obj_map<expr, expr*> beta = bv2lia_rw.cfg().get_lia2bv();
        TRACE("lia2bv", tout << "get_lia2bv:" << std::endl;
        for (obj_map<expr, expr*>::iterator it = beta.begin(); it != beta.end(); ++it) {
            tout << mk_pp(it->m_key, ctx.m()) << " -> " << mk_ismt2_pp(it->m_value, ctx.m()) << std::endl;
        }
        );
        expr_ref foo(make_tree(ctx, lia_exprs),ctx.m());
        compute_interpolant_and_maybe_check(ctx,foo.get(),beta,m_params,false);
        for (ptr_vector<expr_ref>::iterator it = tmp.begin(); it != tmp.end(); ++it){
            delete *it;
        }
    } else {
        // TODO
        obj_map<expr, expr*> beta;
        expr_ref foo(make_tree(ctx, exprs),ctx.m());
        compute_interpolant_and_maybe_check(ctx,foo.get(),beta,m_params,false);
    }
}


// UNARY_CMD(get_interpolant_cmd, "get-interpolant", "<fmla>", "get interpolant for marked positions in fmla", CPK_EXPR, expr *, get_interpolant(ctx, arg););

// UNARY_CMD(get_and_check_interpolant_cmd, "get-and-check-interpolant", "<fmla>", "get and check interpolant for marked positions in fmla", CPK_EXPR, expr *, get_and_check_interpolant(ctx, arg););

class get_interpolant_cmd : public parametric_cmd {
protected:
    ptr_vector<expr>                   m_targets;
public:
    get_interpolant_cmd(char const * name = "get-interpolant"):parametric_cmd(name) {}

    virtual char const * get_usage() const { return "<fmla>+"; }

    virtual char const * get_main_descr() const { 
        return "get interpolant for formulas";
    }
    
    virtual void init_pdescrs(cmd_context & ctx, param_descrs & p) {
    }
    
    virtual void prepare(cmd_context & ctx) { 
        parametric_cmd::prepare(ctx);
        m_targets.resize(0);
    }

    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const {
        TRACE("bv2lia", tout << "in get_interpolant_cmd.next_arg_kind\n";);
        return CPK_EXPR;
    }
    
    virtual void set_next_arg(cmd_context & ctx, expr * arg) {
        TRACE("bv2lia", tout << "in set_next_arg: " << mk_pp(arg, ctx.m()) << "\n";);
        m_targets.push_back(arg);
    }
    
    virtual void execute(cmd_context & ctx) {
        get_interpolant(ctx,m_targets,m_params);
    }
};

class compute_interpolant_cmd : public get_interpolant_cmd {
    mutable unsigned     m_arg_idx;
public:
    compute_interpolant_cmd(char const * name = "compute-interpolant"): 
      get_interpolant_cmd(name) {}
    
    virtual void prepare(cmd_context & ctx) {
        m_arg_idx = 0;
    }

    virtual void init_pdescrs(cmd_context & ctx, param_descrs & p) {
        p.insert("use-bv2lia", CPK_BOOL, "(default: false)");
    }

    virtual void set_next_arg(cmd_context & ctx, expr * arg) {
        TRACE("bv2lia", tout << "in compute_interpolant_cmd.set_next_arg expr: " << mk_pp(arg, ctx.m()) << ", m_arg_idx: " << m_arg_idx << "\n";);
        if (m_arg_idx < 2)
            m_targets.push_back(arg);
        ++m_arg_idx;
    }
     
    virtual void set_next_arg(cmd_context & ctx, symbol const & s) { 
        TRACE("bv2lia", tout << "in compute_interpolant_cmd.set_next_arg symbol: " << s << ", m_arg_idx: " << m_arg_idx << "\n";);

        m_params.set_bool(s, true);
        m_last = symbol::null;
    }
        
    virtual cmd_arg_kind next_arg_kind(cmd_context & ctx) const {
        TRACE("bv2lia", tout << "in compute_interpolant_cmd.next_arg_kind, m_arg_idx: " << m_arg_idx << "\n";);
        if (m_arg_idx < 2)
            return CPK_EXPR;
        else
            return parametric_cmd::next_arg_kind(ctx);
    }
    
    virtual void execute(cmd_context & ctx) {      
        compute_interpolant(ctx,m_targets,m_params);
    }

};

void install_interpolant_cmds(cmd_context & ctx) {
    ctx.insert(alloc(get_interpolant_cmd));
    ctx.insert(alloc(compute_interpolant_cmd));
    //    ctx.insert(alloc(get_and_check_interpolant_cmd));
}
