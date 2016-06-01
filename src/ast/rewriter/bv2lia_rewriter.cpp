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

    int_sort = m_arith_util.mk_int();
}

bv2lia_rewriter_cfg::~bv2lia_rewriter_cfg() {
}

void bv2lia_rewriter_cfg::reset() {
    m_side_conditions.reset();
}

br_status bv2lia_rewriter_cfg::reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
    result_pr = 0;
    TRACE("bv2lia", tout << f->get_name() << " (" << num << ") ";
          for (unsigned i = 0; i < num; ++i) tout << mk_pp(args[i], m()) << " ";
          tout << "\n";);

    expr* stack_el = m_stack.back();
    TRACE("bv2lia", tout << "stack element: " << mk_ismt2_pp(stack_el, m()) << std::endl;);
    m_stack.pop_back();

    if (num == 0 && f->get_family_id() == null_family_id && m_bv_util.is_bv_sort(f->get_range())) {
        unsigned sz;
        result = fresh_var(m().mk_const(f), sz);
        m_bv2sz.insert(result, sz);
        TRACE("bv2lia", tout << "lia var " << mk_pp(result, m()) << " -> bv var (" << f->get_name() << sz << ")" << std::endl;);
        m_lia2bv.insert(result, stack_el);
        return BR_DONE;
    }

    if (m().is_eq(f) && m_arith_util.is_int(args[0]) && m_arith_util.is_int(args[1])) {
        SASSERT(num == 2);
        reduce_eq(args[0], args[1], result);
        return BR_DONE;
    } else if (m().is_ite(f) && m_arith_util.is_int(args[1]) && m_arith_util.is_int(args[2])) {
        SASSERT(num == 3);
        reduce_ite(args[0], args[1], args[2], result);
        return BR_DONE;
    }


    if (f->get_family_id() == m_bv_util.get_family_id()) {
        switch (f->get_decl_kind()) {
        case OP_BV_NUM:
            SASSERT(num == 0);
            reduce_bv_num(f, result);
            return BR_DONE;
        case OP_ULEQ:
            SASSERT(num == 2);
            reduce_uleq(args[0], args[1], result);
            return BR_DONE;
        case OP_SLEQ:
            SASSERT(num == 2);
            reduce_sleq(args[0], args[1], result);
            return BR_DONE;
        case OP_SGT:
            SASSERT(num == 2);
            reduce_sleq(args[0], args[1], result);
            result = m().mk_not(result);
            return BR_DONE;
        case OP_SGEQ:
            SASSERT(num == 2);
            reduce_sleq(args[1], args[0], result);
            return BR_DONE;
        case OP_SLT:
            SASSERT(num == 2);
            reduce_sleq(args[1], args[0], result);
            result = m().mk_not(result);
            return BR_DONE;
        case OP_BADD:
            // TODO support varargs?
            reduce_badd(args[0], args[1], result);
            m_lia2bv.insert(result, stack_el);
            return BR_DONE;
        case OP_BMUL:
            // TODO support varargs?
            reduce_mul(f, args[0], args[1], result);
            m_lia2bv.insert(result, stack_el);
            return BR_DONE;
        case OP_CONCAT:
            SASSERT(num == 2);
            reduce_concat(args[0], args[1], result);
            m_lia2bv.insert(result, stack_el);
            return BR_DONE;
        case OP_EXTRACT:
            SASSERT(num == 1);
            reduce_extract(f, args[0], result);
            m_lia2bv.insert(result, stack_el);
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
    //TRACE("bv2lia", tout << "adding " << mk_pp(res, m()) << " -> " << mk_pp(t, m()) << std::endl;);
    //m_lia2bv.insert(res, t);
    return res;
}

// condition 0 <= fresh_var <= upper
expr* bv2lia_rewriter_cfg::fresh_var(rational const & upper) {
    expr* res = m().mk_fresh_const("x", int_sort);
    expr* lcond = m_arith_util.mk_le(m_arith_util.mk_int(0), res);
    expr* rcond = m_arith_util.mk_le(res, m_arith_util.mk_numeral(upper, true));
    expr* side_condition = m().mk_and(lcond, rcond);
    m_side_conditions.push_back(side_condition);
    TRACE("bv2lia", tout << "side_condition: " << mk_pp(side_condition, m()) << std::endl;);
    return res;
}

func_decl* bv2lia_rewriter_cfg::fresh_func(func_decl* f) {
    func_decl *res;
    if (m_bvop2uf.find(f, res)) {
        TRACE("bv2lia", tout << "retrieved " << mk_pp(res, m()) << std::endl;);
        return res;
    }

    sort* domain[2] = { int_sort, int_sort };
    // f : Int x Int -> Int
    res = m_manager.mk_fresh_func_decl("f", "", 2, domain, int_sort);

    TRACE("bv2lia", tout << "adding " << mk_pp(f, m()) << " -> " << mk_pp(res, m()) << std::endl;);
    m_bvop2uf.insert(f, res);
    return res;
}

// FIXME refactor: how is it different from fresh_var?
expr* bv2lia_rewriter_cfg::add_side_condition(expr* t, rational const & upper) {
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

void bv2lia_rewriter_cfg::reduce_ite(expr* cond, expr * arg1, expr * arg2, expr_ref & result) {
    //TRACE("bv2lia", tout << "reduce_ite: " << mk_pp(arg1, m()) << ", " << mk_pp(arg2, m()) << std::endl;);
    SASSERT(m().is_bool(cond));
    SASSERT(m_arith_util.is_int(arg1));
    SASSERT(m_arith_util.is_int(arg2));

    unsigned sz_arg1;
    if (!m_bv2sz.find(arg1, sz_arg1)) {
        TRACE("bv2lia", tout << "not found: " << mk_pp(arg1, m()) << std::endl;);
        SASSERT(false);
    }
    TRACE("bv2lia", tout << "retrieved size: " << sz_arg1 << std::endl;);

    result = m().mk_ite(cond, arg1, arg2);
    m_bv2sz.insert(result, sz_arg1);
    TRACE("bv2lia", tout << "reduce_ite result: " << mk_pp(result, m()) << std::endl;);
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

void bv2lia_rewriter_cfg::reduce_extract(func_decl * f, expr * arg, expr_ref & result) {
    int i = f->get_parameter(0).get_int();
    int j = f->get_parameter(1).get_int();
    SASSERT(i >= j);
    TRACE("bv2lia", tout << "reduce_extract: " << mk_pp(arg, m()) << " " << i << " " << j << std::endl;);
    SASSERT(m_arith_util.is_int(arg));

    int new_sz = i - j + 1;

    unsigned sz_arg;
    if (!m_bv2sz.find(arg, sz_arg)) {
        TRACE("bv2lia", tout << "not found: " << mk_pp(arg, m()) << std::endl;);
        SASSERT(false);
    }
    TRACE("bv2lia", tout << "retrieved size: " << sz_arg << std::endl;);

    expr* lia_l = fresh_var(rational::power_of_two(i) - rational(1));
    expr* lia_m = fresh_var(rational::power_of_two(new_sz) - rational(1));
    expr* lia_h = fresh_var(rational::power_of_two(sz_arg-i-1) - rational(1));

    expr* mul1 = m_arith_util.mk_mul(m_arith_util.mk_numeral(rational::power_of_two(i+1), true), lia_h);
    expr* mul2 = m_arith_util.mk_mul(m_arith_util.mk_numeral(rational::power_of_two(j), true), lia_m);
    expr* add = m_arith_util.mk_add(mul1, mul2, lia_l);
    
    add_side_condition(add, rational::power_of_two(sz_arg) - rational(1)); // x_t1
    result = add_side_condition(lia_m, rational::power_of_two(new_sz) - rational(1)); // x_t
    m_bv2sz.insert(result, new_sz);
    TRACE("bv2lia", tout << "inserted " << mk_pp(result, m()) << " -> " << new_sz << std::endl;);
    TRACE("bv2lia", tout << "reduce_extract result: " << mk_pp(result, m()) << std::endl;);
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
    expr* add = m_arith_util.mk_add(arg1, arg2);
    expr* sub = m_arith_util.mk_sub(add, mul);

    // TODO add to all the arithmetic operations
    result = add_side_condition(sub, rational::power_of_two(sz_arg1) - rational(1));
    m_bv2sz.insert(result, sz_arg1);
    TRACE("bv2lia", tout << "inserted " << mk_pp(result, m()) << " -> " << sz_arg1 << std::endl;);
    TRACE("bv2lia", tout << "reduce_badd result: " << mk_pp(result, m()) << std::endl;);
}

void bv2lia_rewriter_cfg::reduce_mul(func_decl * f, expr * arg1, expr * arg2, expr_ref & result) {
    TRACE("bv2lia", tout << "reduce_mul: " << mk_pp(arg1, m()) << ", " << mk_pp(arg2, m()) << std::endl;);
    SASSERT(m_arith_util.is_int(arg1));
    SASSERT(m_arith_util.is_int(arg2));

    rational val1, val2;
    if (!m_arith_util.is_numeral(arg1, val1) && !m_arith_util.is_numeral(arg2, val2)) {
        func_decl* f_mul = fresh_func(f);
        m_uf2bvop.insert(f_mul, f);
        unsigned sz_arg;
        if (!m_bv2sz.find(arg1, sz_arg)) {
            TRACE("bv2lia", tout << "not found: " << mk_pp(arg1, m()) << std::endl;);
            SASSERT(false);
        }
        expr* uf = m().mk_app(f_mul, arg1, arg2);

        // commutativity
        expr* uf2 = m().mk_app(f_mul, arg2, arg1);
        m_side_conditions.push_back(m().mk_eq(uf, uf2));

        result = add_side_condition(uf, rational::power_of_two(sz_arg) - rational(1));
        m_bv2sz.insert(result, sz_arg);
        TRACE("bv2lia", tout << "reduce_mul result: " << mk_pp(result, m()) << std::endl;);
        return;
    }

    expr *arg;
    rational val;
    if (!m_arith_util.is_numeral(arg1, val1) && m_arith_util.is_numeral(arg2, val2)) {
        // x * k
        arg = arg1;
        val = val2;
    } else {
        // k * x // k1 * k2
        arg = arg2;
        val = val1;
    }

    expr* lia_sigma = fresh_var(val);

    unsigned sz_arg;
    if (!m_bv2sz.find(arg, sz_arg)) {
        TRACE("bv2lia", tout << "not found: " << mk_pp(arg, m()) << std::endl;);
        SASSERT(false);
    }
    TRACE("bv2lia", tout << "retrieved size: " << sz_arg << std::endl;);

    expr* mul1 = m_arith_util.mk_mul(m_arith_util.mk_numeral(val, true), arg);
    expr* mul2 = m_arith_util.mk_mul(m_arith_util.mk_numeral(rational::power_of_two(sz_arg), true), lia_sigma);
    expr* sub = m_arith_util.mk_sub(mul1, mul2);

    result = add_side_condition(sub, rational::power_of_two(sz_arg) - rational(1));
    m_bv2sz.insert(result, sz_arg);
    TRACE("bv2lia", tout << "inserted " << mk_pp(result, m()) << " -> " << sz_arg << std::endl;);
    TRACE("bv2lia", tout << "reduce_mul result: " << mk_pp(result, m()) << std::endl;);
}

void bv2lia_rewriter_cfg::reduce_uleq(expr * arg1, expr * arg2, expr_ref & result) {
    //TRACE("bv2lia", tout << "mk_uleq: " << mk_pp(arg1, m()) << ", " << mk_pp(arg2, m()) << std::endl;);
    SASSERT(m_arith_util.is_int(arg1));
    SASSERT(m_arith_util.is_int(arg2));

    result = m_arith_util.mk_le(arg1, arg2);
    TRACE("bv2lia", tout << "reduce_bvule result: " << mk_pp(result, m()) << std::endl;);
}

void bv2lia_rewriter_cfg::reduce_sleq(expr * arg1, expr * arg2, expr_ref & result) {
    //TRACE("bv2lia", tout << "mk_uleq: " << mk_pp(arg1, m()) << ", " << mk_pp(arg2, m()) << std::endl;);
    SASSERT(m_arith_util.is_int(arg1));
    SASSERT(m_arith_util.is_int(arg2));

    unsigned sz_arg;
    if (!m_bv2sz.find(arg1, sz_arg)) {
        TRACE("bv2lia", tout << "not found: " << mk_pp(arg1, m()) << std::endl;);
        SASSERT(false);
    }
    TRACE("bv2lia", tout << "retrieved size: " << sz_arg << std::endl;);
    // TODO assert arg1 sz == arg2 sz

    expr* lower = m_arith_util.mk_numeral(rational::power_of_two(sz_arg-1), true);
    expr* upper = m_arith_util.mk_numeral(rational::power_of_two(sz_arg-1) - rational(1), true);

    expr* cond1 = m().mk_and(m_arith_util.mk_le(arg1, upper),
                             m_arith_util.mk_le(arg2, upper));
    expr* cond2 = m().mk_and(m_arith_util.mk_ge(arg1, lower),
                             m_arith_util.mk_ge(arg2, lower));
    expr* cond = m().mk_or(cond1, cond2);
    expr* then_expr = m_arith_util.mk_le(arg1, arg2);
    expr* else_expr = m_arith_util.mk_ge(arg1, lower);
    result = m().mk_ite(cond, then_expr, else_expr);
    TRACE("bv2lia", tout << "reduce_bvsle result: " << mk_pp(result, m()) << std::endl;);
}

// TODO complement?
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
