/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    lia2bv_rewriter.cpp

Abstract:

    Partial rewriter that rewrites LIA expressions into bit-vectors

Author:

    Matthias Schlaipfer (mschlaipfer) 2016-04-21

Notes:

--*/
#include"cooperate.h"
#include"bv_decl_plugin.h"
#include"arith_decl_plugin.h"
#include"params.h"
#include"ast_util.h"
#include"ast_pp.h"
#include"lia2bv_rewriter.h"
#include"rewriter_def.h"

// [1] C. M. Wintersteiger, Y. Hamadi, and L. de Moura: Efficiently Solving
//     Quantified Bit-Vector Formulas, in Formal Methods in System Design,
//     vol. 42, no. 1, pp. 3-23, Springer, 2013.

lia2bv_rewriter_cfg::lia2bv_rewriter_cfg(ast_manager & m, params_ref const & p) :
    m_manager(m),
    m_out(m),
    m_bindings(m),
    m_bv_util(m),
    m_arith_util(m) {
    updt_params(p);
    // We need to make sure that the mananger has the BV and array plugins loaded.
    symbol s_bv("bv");
    if (!m_manager.has_plugin(s_bv))
        m_manager.register_plugin(s_bv, alloc(bv_decl_plugin));
    symbol s_arith("arith");
    if (!m_manager.has_plugin(s_arith))
        m_manager.register_plugin(s_arith, alloc(arith_decl_plugin));
}

lia2bv_rewriter_cfg::~lia2bv_rewriter_cfg() {
}

void lia2bv_rewriter_cfg::reset() {
}

br_status lia2bv_rewriter_cfg::reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
    result_pr = 0;
    TRACE("lia2bv", tout << f->get_name() << " ";
          for (unsigned i = 0; i < num; ++i) tout << mk_pp(args[i], m()) << " ";
          tout << "\n";);
    if (num == 0 && f->get_family_id() == null_family_id) {
        expr *res;
        if (!m_lia2bv->find(m().mk_const(f), res)) {
            TRACE("lia2bv", tout << "not found: " << f->get_name() << std::endl;);
            SASSERT(false);
        }
        result = res;
        TRACE("lia2bv", tout << "result: " << mk_pp(result, m()) << std::endl;);
        return BR_DONE;
    }
    
    if (num == 2 && f->get_family_id() == null_family_id) {
        func_decl *res;
        if (!m_uf2bvop->find(f, res)) {
            TRACE("lia2bv", tout << "not found: " << f->get_name() << std::endl;);
            SASSERT(false);
        }
        result = m().mk_app(res, args[0], args[1]);
        return BR_DONE;
    }

    if (m().is_eq(f)) {
        SASSERT(num == 2);
        if (m_arith_util.is_int(args[0])) {
            // TODO bit-width from context
            reduce_eq(args[0], args[1], 8, result);
            return BR_DONE;
        }
        return BR_FAILED;
    }


    /* TODO
    if (m().is_ite(f)) {
        SASSERT(num == 3);
        if (m_arith_util.is_int(args[1])) {
            reduce_ite(args[0], args[1], args[2], result);
            return BR_DONE;
        }
        return BR_FAILED;
    }*/
    TRACE("lia2bv", tout << "get_lia2bv:" << std::endl;
    for (obj_map<expr, expr*>::iterator it = m_lia2bv->begin(); it != m_lia2bv->end(); ++it) {
        tout << mk_pp(it->m_key, m()) << " -> " << mk_ismt2_pp(it->m_value, m()) << std::endl;
        tout << mk_ismt2_pp(it->m_value, m()) << " sz: " << m_bv_util.get_bv_size(it->m_value) << std::endl;
    }
    );

    

    if (f->get_family_id() == m_arith_util.get_family_id()) {
        unsigned sz;
        switch (f->get_decl_kind()) {
        case OP_NUM:
            SASSERT(num == 0);
            reduce_num(f, result);
            //return BR_DONE;
            return BR_FAILED;
        case OP_ADD:
            SASSERT(num == 2);
            // TODO support varargs?
            beta_sz(args[0], args[1], sz);
            reduce_add(args[0], args[1], sz, result);
            return BR_DONE;
        case OP_MUL:
            beta_sz(args[0], args[1], sz);
            reduce_mul(args[0], args[1], sz, result);
            return BR_DONE;
        case OP_LE:
            SASSERT(num == 2);
            beta_sz(args[0], args[1], sz);
            reduce_le(args[0], args[1], sz, result);
            return BR_DONE;
        case OP_GE:
            SASSERT(num == 2);
            beta_sz(args[0], args[1], sz);
            reduce_ge(args[0], args[1], sz, result);
            return BR_DONE;
        case OP_LT:
            SASSERT(num == 2);
            beta_sz(args[0], args[1], sz);
            reduce_lt(args[0], args[1], sz, result);
            return BR_DONE;
        case OP_GT:
            SASSERT(num == 2);
            beta_sz(args[0], args[1], sz);
            reduce_gt(args[0], args[1], sz, result);
            return BR_DONE;
        // TODO
        default:
            TRACE("lia2bv", tout << "non-supported operator: " << f->get_name() << "\n";
                  for (unsigned i = 0; i < num; i++) tout << mk_ismt2_pp(args[i], m()) << std::endl;);
            return BR_FAILED;
        }
    }

    return BR_FAILED;
}

// TODO sz and numeral handling unnecessarily messy?
void lia2bv_rewriter_cfg::beta_sz(expr * arg1, expr * arg2, unsigned & sz) {
    TRACE("lia2bv", tout << "beta_sz: " << mk_pp(arg1, m()) << ", " << mk_pp(arg2, m()) << std::endl;);
    rational val1, val2;
    if (!m_arith_util.is_numeral(arg1, val1) && !m_arith_util.is_numeral(arg2, val2)) {
        unsigned sz1;
        sz1 = m_bv_util.get_bv_size(arg1);
        TRACE("lia2bv", tout << "sz1: " << sz1 << std::endl;);
        
        unsigned sz2;
        sz2 = m_bv_util.get_bv_size(arg2);
        TRACE("lia2bv", tout << "sz2: " << sz2 << std::endl;);
        SASSERT(sz1 == sz2);

        sz = sz1;
        return;
    } else if (!m_arith_util.is_numeral(arg1, val1)) {
        sz = m_bv_util.get_bv_size(arg1);
        TRACE("lia2bv", tout << "sz: " << sz << std::endl;);
        return;
    } else if (!m_arith_util.is_numeral(arg2, val2)) {
        sz = m_bv_util.get_bv_size(arg2);
        TRACE("lia2bv", tout << "sz: " << sz << std::endl;);
        return;
    }

    TRACE("lia2bv", tout << "both numeral" << std::endl;);
    // both not numeral
    // TODO round max(arg1, arg2) to next highest power of two and then log_2
    sz = 16;
}

void lia2bv_rewriter_cfg::beta(expr * t, unsigned sz, expr_ref & result) {
    rational val;
    if (m_arith_util.is_numeral(t, val)) {
        result = m_bv_util.mk_numeral(val, sz);
        TRACE("lia2bv", tout << "in beta is_numeral " << val << std::endl;);
        SASSERT(m_bv_util.is_bv(result));
        return;
    }
    TRACE("lia2bv", tout << "in beta not numeral " << mk_pp(t, m()) << std::endl;);
    result = t;
    SASSERT(m_bv_util.is_bv(result));
}

void lia2bv_rewriter_cfg::reduce_eq(expr * arg1, expr * arg2, unsigned sz, expr_ref & result) {
    TRACE("lia2bv", tout << "reduce_eq: " << mk_pp(arg1, m()) << ", " << mk_pp(arg2, m()) << std::endl;);

    expr_ref bv_arg1(m());
    beta(arg1, sz, bv_arg1);

    expr_ref bv_arg2(m());
    beta(arg2, sz, bv_arg2);

    TRACE("lia2bv", tout << "reduce_eq: " << mk_pp(bv_arg1, m()) << ", " << mk_pp(bv_arg2, m()) << std::endl;);
    result = m().mk_eq(bv_arg1, bv_arg2);
    TRACE("lia2bv", tout << "reduce_eq: " << mk_pp(result, m()) << std::endl;);
}

void lia2bv_rewriter_cfg::reduce_add(expr * arg1, expr * arg2, unsigned sz, expr_ref & result) {
    TRACE("lia2bv", tout << "reduce_add: " << mk_pp(arg1, m()) << ", " << mk_pp(arg2, m()) << std::endl;);

    expr_ref bv_arg1(m());
    beta(arg1, sz, bv_arg1);

    expr_ref bv_arg2(m());
    beta(arg2, sz, bv_arg2);

    TRACE("lia2bv", tout << "reduce_add: " << mk_pp(bv_arg1, m()) << ", " << mk_pp(bv_arg2, m()) << std::endl;);
    result = m_bv_util.mk_bv_add(bv_arg1, bv_arg2);
    TRACE("lia2bv", tout << "reduce_add: " << mk_pp(result, m()) << std::endl;);
}

void lia2bv_rewriter_cfg::reduce_mul(expr * arg1, expr * arg2, unsigned sz, expr_ref & result) {
    TRACE("lia2bv", tout << "reduce_mul: " << mk_pp(arg1, m()) << ", " << mk_pp(arg2, m()) << std::endl;);

    expr_ref bv_arg1(m());
    beta(arg1, sz, bv_arg1);

    expr_ref bv_arg2(m());
    beta(arg2, sz, bv_arg2);

    TRACE("lia2bv", tout << "reduce_mul: " << mk_pp(bv_arg1, m()) << ", " << mk_pp(bv_arg2, m()) << std::endl;);
    result = m_bv_util.mk_bv_mul(bv_arg1, bv_arg2);
    TRACE("lia2bv", tout << "reduce_mul: " << mk_pp(result, m()) << std::endl;);
}

void lia2bv_rewriter_cfg::reduce_le(expr * arg1, expr * arg2, unsigned sz, expr_ref & result) {
    TRACE("lia2bv", tout << "reduce_le: " << mk_pp(arg1, m()) << ", " << mk_pp(arg2, m()) << std::endl;);

    expr_ref bv_arg1(m());
    beta(arg1, sz, bv_arg1);

    expr_ref bv_arg2(m());
    beta(arg2, sz, bv_arg2);

    TRACE("lia2bv", tout << "reduce_le: " << mk_pp(bv_arg1, m()) << ", " << mk_pp(bv_arg2, m()) << std::endl;);
    result = m_bv_util.mk_ule(bv_arg1, bv_arg2);
    TRACE("lia2bv", tout << "reduce_le: " << mk_pp(result, m()) << std::endl;);
}

void lia2bv_rewriter_cfg::reduce_ge(expr * arg1, expr * arg2, unsigned sz, expr_ref & result) {
    TRACE("lia2bv", tout << "reduce_ge: " << mk_pp(arg1, m()) << ", " << mk_pp(arg2, m()) << std::endl;);

    expr_ref bv_arg1(m());
    beta(arg1, sz, bv_arg1);

    expr_ref bv_arg2(m());
    beta(arg2, sz, bv_arg2);

    TRACE("lia2bv", tout << "reduce_ge: " << mk_pp(bv_arg1, m()) << ", " << mk_pp(bv_arg2, m()) << std::endl;);
    result = m_bv_util.mk_ule(bv_arg2, bv_arg1);
    TRACE("lia2bv", tout << "reduce_ge: " << mk_pp(result, m()) << std::endl;);
}

void lia2bv_rewriter_cfg::reduce_lt(expr * arg1, expr * arg2, unsigned sz, expr_ref & result) {
    TRACE("lia2bv", tout << "reduce_lt: " << mk_pp(arg1, m()) << ", " << mk_pp(arg2, m()) << std::endl;);

    expr_ref bv_arg1(m());
    beta(arg1, sz, bv_arg1);

    expr_ref bv_arg2(m());
    beta(arg2, sz, bv_arg2);

    TRACE("lia2bv", tout << "reduce_lt: " << mk_pp(bv_arg1, m()) << ", " << mk_pp(bv_arg2, m()) << std::endl;);
    result = m().mk_not(m_bv_util.mk_ule(bv_arg2, bv_arg1));
    TRACE("lia2bv", tout << "reduce_lt: " << mk_pp(result, m()) << std::endl;);
}

void lia2bv_rewriter_cfg::reduce_gt(expr * arg1, expr * arg2, unsigned sz, expr_ref & result) {
    TRACE("lia2bv", tout << "reduce_gt: " << mk_pp(arg1, m()) << ", " << mk_pp(arg2, m()) << std::endl;);

    expr_ref bv_arg1(m());
    beta(arg1, sz, bv_arg1);

    expr_ref bv_arg2(m());
    beta(arg2, sz, bv_arg2);

    TRACE("lia2bv", tout << "reduce_gt: " << mk_pp(bv_arg1, m()) << ", " << mk_pp(bv_arg2, m()) << std::endl;);
    result = m().mk_not(m_bv_util.mk_ule(bv_arg1, bv_arg2));
    TRACE("lia2bv", tout << "reduce_gt: " << mk_pp(result, m()) << std::endl;);
}

void lia2bv_rewriter_cfg::reduce_num(func_decl * arg1, expr_ref & result) {
    //TRACE("lia2bv", tout << "reduce_num: " << arg1->get_parameter(0) << std::endl;);
    //rational v  = arg1->get_parameter(0).get_rational();
    //result = m_bv_util.mk_(v, true);
    //TRACE("lia2bv", tout << "result: " << mk_pp(result, m()) << std::endl;);
}

bool lia2bv_rewriter_cfg::pre_visit(expr * t)
{
    return true;
}

bool lia2bv_rewriter_cfg::reduce_quantifier(quantifier * old_q,
    expr * new_body,
    expr * const * new_patterns,
    expr * const * new_no_patterns,
    expr_ref & result,
    proof_ref & result_pr) {
    NOT_IMPLEMENTED_YET();
    return true;
}

bool lia2bv_rewriter_cfg::reduce_var(var * t, expr_ref & result, proof_ref & result_pr) {
    if (t->get_idx() >= m_bindings.size())
        return false;
    NOT_IMPLEMENTED_YET();
    return true;
}

template class rewriter_tpl<lia2bv_rewriter_cfg>;
