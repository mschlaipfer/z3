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
    extra_assertions(m) {
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
    extra_assertions.reset();
}

br_status bv2lia_rewriter_cfg::reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
    result_pr = 0;
    TRACE("bv2lia", tout << f->get_name() << " ";
          for (unsigned i = 0; i < num; ++i) tout << mk_pp(args[i], m()) << " ";
          tout << "\n";);
    /* TODO
    if (num == 0 && f->get_family_id() == null_family_id && m_bv_util.is_bv_sort(f->get_range())) {
        result = fresh_var(f);
        return BR_DONE;
    }
    */

    if (m().is_eq(f)) {
        SASSERT(num == 2);
        if (m_bv_util.is_bv(args[0])) {
            mk_eq(args[0], args[1], result);
            return BR_DONE;
        }
        return BR_FAILED;
    }


    /* TODO
    if (m().is_ite(f)) {
        SASSERT(num == 3);
        if (m_bv_util.is_bv(args[1])) {
            reduce_ite(args[0], args[1], args[2], result);
            return BR_DONE;
        }
        return BR_FAILED;
    }*/

    if (f->get_family_id() == m_bv_util.get_family_id()) {
        switch (f->get_decl_kind()) {
        case OP_BV_NUM:
            SASSERT(num == 0);
            mk_bv_num(f, result);
            return BR_DONE;
        case OP_BADD:
            // TODO support varargs?
            mk_badd(args[0], args[1], result);
            return BR_DONE;
        /*
        case OP_BMUL:
            if (!m_blast_mul)
                return BR_FAILED;
            reduce_mul(num, args, result);
            return BR_DONE;
        */
        case OP_CONCAT:
            SASSERT(num == 2);
            mk_concat(args[0], args[1], result);
            return BR_DONE;
        case OP_ULEQ:
            SASSERT(num == 2);
            mk_uleq(args[0], args[1], result);
            return BR_DONE;
        // TODO
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

expr* bv2lia_rewriter_cfg::fresh_var(expr* t, unsigned &sz) {
    sz = m_bv_util.get_bv_size(t);
    expr *res;
    if (m_const2lia.find(t, res)) {
        TRACE("bv2lia", tout << "retrieved " << mk_pp(t, m()) << std::endl;);
        return res;
    }

    res = fresh_var(sz);

    TRACE("bv2lia", tout << "adding " << mk_pp(t, m()) << std::endl;);
    m_const2lia.insert(t, res);
    return res;
}

expr* bv2lia_rewriter_cfg::fresh_var(unsigned sz) {
    expr* res = m_manager.mk_fresh_const("x", m_arith_util.mk_int());
    expr* lcond = m_arith_util.mk_le(m_arith_util.mk_int(0), res);
    expr* rcond = m_arith_util.mk_le(res, m_arith_util.mk_numeral(power(rational(2), sz) - rational(1), true));
    expr* side_condition = m_manager.mk_and(lcond, rcond);
    extra_assertions.push_back(side_condition);
    TRACE("bv2lia", tout << "side_condition: " << mk_pp(side_condition, m()) << std::endl;);
    return res;
}

// TODO
void bv2lia_rewriter_cfg::mk_eq(expr * arg1, expr * arg2, expr_ref & result) {
    TRACE("bv2lia", tout << "mk_eq: " << mk_pp(arg1, m()) << ", " << mk_pp(arg2, m()) << std::endl;);

    expr* lia_x1;
    if(m_bv_util.is_bv(arg1)) {
        lia_x1 = fresh_var(arg1);
    } else {
        lia_x1 = arg1;
    }

    expr* lia_x2;
    if(m_bv_util.is_bv(arg2)) {
        lia_x2 = fresh_var(arg2);
    } else {
        lia_x2 = arg2;
    }

    result = m_arith_util.mk_eq(lia_x1, lia_x2);
    TRACE("bv2lia", tout << "mk_eq result: " << mk_pp(result, m()) << std::endl;);
}

// TODO
// reuse fresh_var for same expr
void bv2lia_rewriter_cfg::mk_concat(expr * arg1, expr * arg2, expr_ref & result) {
    SASSERT(m_bv_util.is_bv(arg1));
    SASSERT(m_bv_util.is_bv(arg2));
    TRACE("bv2lia", tout << "mk_concat: " << mk_pp(arg1, m()) << ", " << mk_pp(arg2, m()) << std::endl;);
    unsigned sz_arg1;
    expr* lia_x1 = fresh_var(arg1, sz_arg1);

    unsigned sz_arg2;
    expr* lia_x2 = fresh_var(arg2, sz_arg2);
    TRACE("bv2lia", tout << "before lexpr " << std::endl;);

    //expr* lexpr = fresh_var(sz_arg1 + sz_arg2);
    expr* rexpr = m_arith_util.mk_add(m_arith_util.mk_mul(lia_x1, m_arith_util.mk_numeral(power(rational(2), sz_arg2), true)), lia_x2);
    //result = m_arith_util.mk_eq(lexpr, rexpr);
    result = rexpr;
    TRACE("bv2lia", tout << "mk_concat result: " << mk_pp(result, m()) << std::endl;);
}

// TODO
void bv2lia_rewriter_cfg::mk_badd(expr * arg1, expr * arg2, expr_ref & result) {
    TRACE("bv2lia", tout << "mk_badd: " << mk_pp(arg1, m()) << ", " << mk_pp(arg2, m()) << std::endl;);

    unsigned sz_arg1;
    expr* lia_x1;
    if(m_bv_util.is_bv(arg1)) {
        lia_x1 = fresh_var(arg1, sz_arg1);
    } else {
        // TODO
        sz_arg1 = 8;
        lia_x1 = arg1;
    }

    unsigned sz_arg2;
    expr* lia_x2;
    if(m_bv_util.is_bv(arg2)) {
        lia_x2 = fresh_var(arg2, sz_arg2);
    } else {
        // TODO
        sz_arg2 = 8;
        lia_x2 = arg2;
    }
    SASSERT(sz_arg1 == sz_arg2);
    
    expr* lia_sigma = fresh_var(1);

    expr* mul = m_arith_util.mk_mul(m_arith_util.mk_numeral(power(rational(2), sz_arg1), true), lia_sigma);
    expr* sub = m_arith_util.mk_sub(lia_x2, mul);
    result = m_arith_util.mk_add(lia_x1, sub);
    TRACE("bv2lia", tout << "mk_bvadd result: " << mk_pp(result, m()) << std::endl;);
}

// TODO
void bv2lia_rewriter_cfg::mk_uleq(expr * arg1, expr * arg2, expr_ref & result) {
    TRACE("bv2lia", tout << "mk_uleq: " << mk_pp(arg1, m()) << ", " << mk_pp(arg2, m()) << std::endl;);

    unsigned sz_arg1;
    expr* lia_x1;
    if(m_bv_util.is_bv(arg1)) {
        lia_x1 = fresh_var(arg1, sz_arg1);
    } else {
        // TODO
        sz_arg1 = 8;
        lia_x1 = arg1;
    }

    unsigned sz_arg2;
    expr* lia_x2;
    if(m_bv_util.is_bv(arg2)) {
        lia_x2 = fresh_var(arg2, sz_arg2);
    } else {
        // TODO
        sz_arg2 = 8;
        lia_x2 = arg2;
    }
    SASSERT(sz_arg1 == sz_arg2);

    result = m_arith_util.mk_le(lia_x1, lia_x2);

    TRACE("bv2lia", tout << "mk_bvule result: " << mk_pp(result, m()) << std::endl;);
}

void bv2lia_rewriter_cfg::mk_bv_num(func_decl * arg1, expr_ref & result) {
    rational val = arg1->get_parameter(0).get_rational();
    TRACE("bv2lia", tout << "mk_bv_num:" << val << std::endl;);
    result = m_arith_util.mk_numeral(val, true);
}

expr* bv2lia_rewriter_cfg::mk_extend(unsigned sz, expr* b, bool is_signed) {
    if (sz == 0) {
        return b;
    }
    rational r;
    unsigned bv_sz;
    if (is_signed) {
        return m_bv_util.mk_sign_extend(sz, b);
    }
    else if (m_bv_util.is_numeral(b, r, bv_sz)) {
        return m_bv_util.mk_numeral(r, bv_sz + sz);
    }
    else {
        return m_bv_util.mk_zero_extend(sz, b);
    }
}


void bv2lia_rewriter_cfg::align_sizes(expr_ref& s, expr_ref& t, bool is_signed) {
    unsigned sz1 = m_bv_util.get_bv_size(s);
    unsigned sz2 = m_bv_util.get_bv_size(t);
    if (sz1 > sz2 && is_signed) {
        t = mk_extend(sz1-sz2, t, true);
    }
    if (sz1 > sz2 && !is_signed) {
        t = mk_extend(sz1-sz2, t, false);
    }
    if (sz1 < sz2 && is_signed) {
        s = mk_extend(sz2-sz1, s, true);
    }
    if (sz1 < sz2 && !is_signed) {
        s = mk_extend(sz2-sz1, s, false);
    }
}


bool bv2lia_rewriter_cfg::is_zero(expr* n) {
    rational r;
    unsigned sz;
    return m_bv_util.is_numeral(n, r, sz) && r.is_zero();
}

bool bv2lia_rewriter_cfg::pre_visit(expr * t)
{
    TRACE("bv2lia_rw_q", tout << "pre_visit: " << mk_ismt2_pp(t, m()) << std::endl;);

    if (is_quantifier(t)) {
        quantifier * q = to_quantifier(t);
        TRACE("bv2lia_rw_q", tout << "pre_visit quantifier [" << q->get_id() << "]: " << mk_ismt2_pp(q->get_expr(), m()) << std::endl;);
        sort_ref_vector new_bindings(m_manager);
        for (unsigned i = 0; i < q->get_num_decls(); i++)
            new_bindings.push_back(q->get_decl_sort(i));
        SASSERT(new_bindings.size() == q->get_num_decls());
        m_bindings.append(new_bindings);
    }
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
