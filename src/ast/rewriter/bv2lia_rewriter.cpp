/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    bv2lia_rewriter.cpp

Abstract:

    Rewriter that rewrites bit-vectors into LIA expressions.

Author:

    Matthias Schlaipfer (mschlaipfer) 2016-04-18

Notes:

--*/
#include"cooperate.h"
#include"bv_decl_plugin.h"
#include"arith_decl_plugin.h"
#include"params.h"
#include"ast_util.h"
#include"ast_pp.h"
#include"bv2lia_rewriter.h"
#include"rewriter_def.h"

// [1] C. M. Wintersteiger, Y. Hamadi, and L. de Moura: Efficiently Solving
//     Quantified Bit-Vector Formulas, in Formal Methods in System Design,
//     vol. 42, no. 1, pp. 3-23, Springer, 2013.

bv2lia_rewriter_cfg::bv2lia_rewriter_cfg(ast_manager & m, params_ref const & p) :
    m_manager(m),
    m_out(m),
    m_bindings(m),
    m_bv_util(m),
    m_arith_util(m),
    m_side_conditions(m),
    m_stack(m) {
    updt_params(p);
    // We need to make sure that the mananger has the BV and array plugins loaded.
    symbol s_bv("bv");
    if (!m_manager.has_plugin(s_bv))
        m_manager.register_plugin(s_bv, alloc(bv_decl_plugin));
    symbol s_arith("arith");
    if (!m_manager.has_plugin(s_arith))
        m_manager.register_plugin(s_arith, alloc(arith_decl_plugin));
}

bv2lia_rewriter_cfg::~bv2lia_rewriter_cfg() {
}

void bv2lia_rewriter_cfg::reset() {
    m_side_conditions.reset();
}

br_status bv2lia_rewriter_cfg::reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
    result_pr = 0;
    TRACE("bv2lia", tout << f->get_name() << " ";
          for (unsigned i = 0; i < num; ++i) tout << mk_pp(args[i], m()) << " ";
          tout << "\n";);

    expr* stack_el = m_stack.back();
    TRACE("bv2lia", tout << "stack element: " << mk_ismt2_pp(stack_el, m()) << std::endl;);
    m_stack.pop_back();

    if (num == 0 && f->get_family_id() == null_family_id && m_bv_util.is_bv_sort(f->get_range())) {
        sort * s = f->get_range();
        unsigned sz = m_bv_util.get_bv_size(s);
        result = fresh_var(m().mk_const(f), sz);
        m_bv2sz.insert(result, sz);
        //TRACE("bv2lia", tout << "inserted " << mk_pp(a, m()) << " -> " << sz << std::endl;);
        TRACE("bv2lia", tout << "inserted " << mk_pp(f, m()) << " -> " << sz << std::endl;);
        TRACE("bv2lia", tout << "inserted " << mk_pp(result, m()) << " -> " << sz << std::endl;);
        return BR_DONE;
    }

    if (m().is_eq(f)) {
        SASSERT(num == 2);
        reduce_eq(args[0], args[1], result);
        return BR_DONE;
    }


    if (f->get_family_id() == m_bv_util.get_family_id()) {
        switch (f->get_decl_kind()) {
        case OP_BV_NUM:
            SASSERT(num == 0);
            reduce_bv_num(f, result);
            return BR_DONE;
        case OP_BADD:
            // TODO support varargs?
            reduce_badd(args[0], args[1], result);
            return BR_DONE;
        case OP_CONCAT:
            SASSERT(num == 2);
            reduce_concat(args[0], args[1], result);
            return BR_DONE;
        case OP_ULEQ:
            SASSERT(num == 2);
            reduce_uleq(args[0], args[1], result);
            return BR_DONE;
        // TODO operator support
        default:
            TRACE("bv2lia", tout << "non-supported operator: " << f->get_name() << "\n";
                  for (unsigned i = 0; i < num; i++) tout << mk_ismt2_pp(args[i], m()) << std::endl;);
            return BR_FAILED;
        }
    }

    return BR_FAILED;
}

expr* bv2lia_rewriter_cfg::fresh_var(expr* t) {
    unsigned sz;
    return fresh_var(t, sz);
}

// condition 0 <= fresh_var <= sz
expr* bv2lia_rewriter_cfg::fresh_var(expr* t, unsigned &sz) {
    sz = m_bv_util.get_bv_size(t);
    expr *res;
    if (m_bv2lia.find(t, res)) {
        TRACE("bv2lia", tout << "retrieved " << mk_pp(t, m()) << std::endl;);
        return res;
    }

    res = fresh_var(rational::power_of_two(sz) - rational(1));

    TRACE("bv2lia", tout << "adding " << mk_pp(t, m()) << " -> " << mk_pp(res, m()) << std::endl;);
    m_bv2lia.insert(t, res);
    TRACE("bv2lia", tout << "adding " << mk_pp(res, m()) << " -> " << mk_pp(t, m()) << std::endl;);
    m_lia2bv.insert(res, t);
    return res;
}

// condition 0 <= fresh_var <= upper
expr* bv2lia_rewriter_cfg::fresh_var(rational const & upper) {
    expr* res = m().mk_fresh_const("x", m_arith_util.mk_int());
    expr* lcond = m_arith_util.mk_le(m_arith_util.mk_int(0), res);
    expr* rcond = m_arith_util.mk_le(res, m_arith_util.mk_numeral(upper, true));
    expr* side_condition = m().mk_and(lcond, rcond);
    m_side_conditions.push_back(side_condition);
    TRACE("bv2lia", tout << "side_condition: " << mk_pp(side_condition, m()) << std::endl;);
    return res;
}

expr* bv2lia_rewriter_cfg::add_side_condition(expr* t, rational const & upper) {
    // TODO map fresh var here to stack element for lia2bv rewriter?
    expr* res = m().mk_fresh_const("x", m_arith_util.mk_int());
    expr* side_condition1 = m_arith_util.mk_eq(res, t);
    m_side_conditions.push_back(side_condition1);
    TRACE("bv2lia", tout << "side_condition1: " << mk_pp(side_condition1, m()) << std::endl;);

    expr* lcond = m_arith_util.mk_le(m_arith_util.mk_int(0), res);
    expr* rcond = m_arith_util.mk_le(res, m_arith_util.mk_numeral(upper, true));
    expr* side_condition2 = m().mk_and(lcond, rcond);
    m_side_conditions.push_back(side_condition2);
    TRACE("bv2lia", tout << "side_condition2: " << mk_pp(side_condition2, m()) << std::endl;);
    return res;
}

void bv2lia_rewriter_cfg::reduce_eq(expr * arg1, expr * arg2, expr_ref & result) {
    //TRACE("bv2lia", tout << "reduce_eq: " << mk_pp(arg1, m()) << ", " << mk_pp(arg2, m()) << std::endl;);
    SASSERT(m_arith_util.is_int(arg1));
    SASSERT(m_arith_util.is_int(arg2));

    result = m_arith_util.mk_eq(arg1, arg2);
    TRACE("bv2lia", tout << "reduce_eq result: " << mk_pp(result, m()) << std::endl;);
}

void bv2lia_rewriter_cfg::reduce_concat(expr * arg1, expr * arg2, expr_ref & result) {
    //TRACE("bv2lia", tout << "reduce_concat: " << mk_pp(arg1, m()) << ", " << mk_pp(arg2, m()) << std::endl;);
    SASSERT(m_arith_util.is_int(arg1));
    SASSERT(m_arith_util.is_int(arg2));

    unsigned sz_arg1;
    if (!m_bv2sz.find(arg1, sz_arg1)) {
        TRACE("bv2lia", tout << "not found: " << mk_pp(arg1, m()) << std::endl;);
        SASSERT(false);
    }
    TRACE("bv2lia", tout << "retrieved size: " << sz_arg1 << std::endl;);

    unsigned sz_arg2;
    if (!m_bv2sz.find(arg2, sz_arg2)) {
        TRACE("bv2lia", tout << "not found: " << mk_pp(arg2, m()) << std::endl;);
        SASSERT(false);
    }
    TRACE("bv2lia", tout << "retrieved size: " << sz_arg2 << std::endl;);

    expr* rexpr = m_arith_util.mk_add(m_arith_util.mk_mul(arg1, m_arith_util.mk_numeral(rational::power_of_two(sz_arg2), true)), arg2);
    result = add_side_condition(rexpr, rational::power_of_two(sz_arg1 + sz_arg2) - rational(1));
    m_bv2sz.insert(result, sz_arg1 + sz_arg2);
    TRACE("bv2lia", tout << "inserted " << mk_pp(result, m()) << " -> " << sz_arg1 + sz_arg2 << std::endl;);
    TRACE("bv2lia", tout << "mk_concat result: " << mk_pp(result, m()) << std::endl;);
}

void bv2lia_rewriter_cfg::reduce_badd(expr * arg1, expr * arg2, expr_ref & result) {
    //TRACE("bv2lia", tout << "mk_badd: " << mk_pp(arg1, m()) << ", " << mk_pp(arg2, m()) << std::endl;);
    SASSERT(m_arith_util.is_int(arg1));
    SASSERT(m_arith_util.is_int(arg2));

    unsigned sz_arg1;
    if (!m_bv2sz.find(arg1, sz_arg1)) {
        TRACE("bv2lia", tout << "not found: " << mk_pp(arg1, m()) << std::endl;);
        SASSERT(false);
    }
    TRACE("bv2lia", tout << "retrieved size: " << sz_arg1 << std::endl;);

    unsigned sz_arg2;
    if (!m_bv2sz.find(arg2, sz_arg2)) {
        TRACE("bv2lia", tout << "not found: " << mk_pp(arg2, m()) << std::endl;);
        SASSERT(false);
    }
    TRACE("bv2lia", tout << "retrieved size: " << sz_arg2 << std::endl;);

    SASSERT(sz_arg1 == sz_arg2);
    
    expr* lia_sigma = fresh_var(rational(1));

    expr* mul = m_arith_util.mk_mul(m_arith_util.mk_numeral(rational::power_of_two(sz_arg1), true), lia_sigma);
    expr* sub = m_arith_util.mk_sub(arg2, mul);
    expr* add = m_arith_util.mk_add(arg1, sub);

    // TODO add to all the arithmetic operations
    result = add_side_condition(add, rational::power_of_two(sz_arg1) - rational(1));
    m_bv2sz.insert(result, sz_arg1);
    TRACE("bv2lia", tout << "inserted " << mk_pp(result, m()) << " -> " << sz_arg1 << std::endl;);
    TRACE("bv2lia", tout << "mk_bvadd result: " << mk_pp(result, m()) << std::endl;);
}

void bv2lia_rewriter_cfg::reduce_uleq(expr * arg1, expr * arg2, expr_ref & result) {
    //TRACE("bv2lia", tout << "mk_uleq: " << mk_pp(arg1, m()) << ", " << mk_pp(arg2, m()) << std::endl;);
    SASSERT(m_arith_util.is_int(arg1));
    SASSERT(m_arith_util.is_int(arg2));

    unsigned sz_arg1;
    if (!m_bv2sz.find(arg1, sz_arg1)) {
        TRACE("bv2lia", tout << "not found: " << mk_pp(arg1, m()) << std::endl;);
        SASSERT(false);
    }
    TRACE("bv2lia", tout << "retrieved size: " << sz_arg1 << std::endl;);

    unsigned sz_arg2;
    if (!m_bv2sz.find(arg2, sz_arg2)) {
        TRACE("bv2lia", tout << "not found: " << mk_pp(arg2, m()) << std::endl;);
        SASSERT(false);
    }
    TRACE("bv2lia", tout << "retrieved size: " << sz_arg2 << std::endl;);

    SASSERT(sz_arg1 == sz_arg2);

    result = m_arith_util.mk_le(arg1, arg2);

    TRACE("bv2lia", tout << "reduce_bvule result: " << mk_pp(result, m()) << std::endl;);
}

void bv2lia_rewriter_cfg::reduce_bv_num(func_decl * arg1, expr_ref & result) {
    //TRACE("bv2lia", tout << "reduce_bv_num:" << val << std::endl;);
    rational v  = arg1->get_parameter(0).get_rational();
    unsigned sz = arg1->get_parameter(1).get_int();
    result = m_arith_util.mk_numeral(v, true);
    m_bv2sz.insert(result, sz);
    TRACE("bv2lia", tout << "inserted " << mk_pp(result, m()) << " -> " << sz << std::endl;);
    TRACE("bv2lia", tout << "reduce_bv_num result:" << result << std::endl;);
}

bool bv2lia_rewriter_cfg::pre_visit(expr * t)
{
    TRACE("bv2lia", tout << "pre_visit: " << mk_ismt2_pp(t, m()) << std::endl;);

    m_stack.push_back(t);

    return true;
}

bool bv2lia_rewriter_cfg::reduce_quantifier(quantifier * old_q,
    expr * new_body,
    expr * const * new_patterns,
    expr * const * new_no_patterns,
    expr_ref & result,
    proof_ref & result_pr) {
    NOT_IMPLEMENTED_YET();
    return true;
}

bool bv2lia_rewriter_cfg::reduce_var(var * t, expr_ref & result, proof_ref & result_pr) {
    if (t->get_idx() >= m_bindings.size())
        return false;
    NOT_IMPLEMENTED_YET();
    return true;
}

template class rewriter_tpl<bv2lia_rewriter_cfg>;
