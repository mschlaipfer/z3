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

bv2lia_rewriter_cfg::~bv2lia_rewriter_cfg() {
}

void bv2lia_rewriter_cfg::reset() {}

br_status bv2lia_rewriter_cfg::reduce_app(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result, proof_ref & result_pr) {
    TRACE("bv2lia", tout << "reduce_app: " << mk_pp(f, m()) << std::endl;);
    if (f->get_family_id() == m_arith_util.get_family_id()) {
        switch (f->get_decl_kind()) {
        case OP_NUM:  return BR_FAILED;
        case OP_LE:   SASSERT(num_args == 2); return mk_le(args[0], args[1], result);
        case OP_GE:   SASSERT(num_args == 2); return mk_ge(args[0], args[1], result);
        case OP_LT:   SASSERT(num_args == 2); return mk_lt(args[0], args[1], result);
        case OP_GT:   SASSERT(num_args == 2); return mk_gt(args[0], args[1], result);
        case OP_ADD:  return mk_add(num_args, args, result);
        case OP_MUL:  return mk_mul(num_args, args, result);
        case OP_SUB:  return mk_sub(num_args, args, result);
        case OP_DIV:  return BR_FAILED;
        case OP_IDIV: SASSERT(num_args == 2); return mk_idiv(args[0], args[1], result);
        case OP_MOD:  SASSERT(num_args == 2); return mk_mod(args[0], args[1], result);
        case OP_REM:  SASSERT(num_args == 2); return mk_rem(args[0], args[1], result);
        case OP_UMINUS:  SASSERT(num_args == 1); return mk_uminus(args[0], result);
        case OP_TO_REAL: return BR_FAILED;
        case OP_TO_INT:  return BR_FAILED;
        case OP_IS_INT:  return BR_FAILED;
        default:         return BR_FAILED;
        }
    }
    if (f->get_family_id() == m().get_basic_family_id()) {
        switch (f->get_decl_kind()) {
        case OP_EQ:  SASSERT(num_args == 2); return mk_eq(args[0], args[1], result);
        case OP_ITE: SASSERT(num_args == 3); return mk_ite(args[0], args[1], args[2], result); 
        case OP_DISTINCT: 
            if (num_args >= 2 && m_arith_util.is_int(args[0])) {
                expr_ref_vector eqs(m());
                for (unsigned i = 0; i < num_args; ++i) {
                    for (unsigned j = i + 1; j < num_args; ++j) {
                        if (BR_DONE != mk_eq(args[i], args[j], result)) {
                            return BR_FAILED;
                        }
                        eqs.push_back(result);
                    }
                }
                result = m().mk_not(mk_or(eqs));
                return BR_DONE;
            }
            return BR_FAILED;
        default: return BR_FAILED;
        }
    }
    return BR_FAILED;
}

br_status bv2lia_rewriter_cfg::mk_le(expr * s, expr * t, expr_ref & result) {
    // TODO
    TRACE("bv2lia", tout << "mk_le: " << mk_pp(s, m()) << ", " << mk_pp(t, m()) << std::endl;);
    return BR_FAILED;
}

br_status bv2lia_rewriter_cfg::mk_lt(expr * arg1, expr * arg2, expr_ref & result) {
    // TODO
    TRACE("bv2lia", tout << "mk_lt: " << mk_pp(arg1, m()) << ", " << mk_pp(arg2, m()) << std::endl;);
    return BR_REWRITE2;
}

br_status bv2lia_rewriter_cfg::mk_ge(expr * arg1, expr * arg2, expr_ref & result) {
    // TODO
    TRACE("bv2lia", tout << "mk_ge: " << mk_pp(arg1, m()) << ", " << mk_pp(arg2, m()) << std::endl;);
    return mk_le(arg2, arg1, result);
}

br_status bv2lia_rewriter_cfg::mk_gt(expr * arg1, expr * arg2, expr_ref & result) {
    // TODO
    TRACE("bv2lia", tout << "mk_gt: " << mk_pp(arg1, m()) << ", " << mk_pp(arg2, m()) << std::endl;);
    result = m().mk_not(m_arith_util.mk_le(arg1, arg2));
    return BR_REWRITE2;
}

br_status bv2lia_rewriter_cfg::mk_ite(expr* c, expr* s, expr* t, expr_ref& result) {
    // TODO
    TRACE("bv2lia", tout << "mk_ite: " << mk_pp(c, m()) << ", " << mk_pp(s, m()) << ", " << mk_pp(t, m()) << std::endl;);
    return BR_FAILED;
}

br_status bv2lia_rewriter_cfg::mk_eq(expr * s, expr * t, expr_ref & result) {
    // TODO
    TRACE("bv2lia", tout << "mk_eq: " << mk_pp(s, m()) << ", " << mk_pp(t, m()) << std::endl;);
    return BR_FAILED;
}


br_status bv2lia_rewriter_cfg::mk_idiv(expr * arg1, expr * arg2, expr_ref & result) {
    // TODO
    return BR_FAILED;
}
 
br_status bv2lia_rewriter_cfg::mk_mod(expr * s, expr * t, expr_ref & result) {
    // TODO
    return BR_FAILED;
}


br_status bv2lia_rewriter_cfg::mk_rem(expr * arg1, expr * arg2, expr_ref & result) {
    // TODO
    return BR_FAILED;
}

br_status bv2lia_rewriter_cfg::mk_uminus(expr * s, expr_ref & result) {
    // TODO
    return BR_FAILED;
}


br_status bv2lia_rewriter_cfg::mk_add(unsigned num_args, expr * const* args, expr_ref& result) {
    // TODO
    return BR_FAILED;
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

expr* bv2lia_rewriter_cfg::mk_bv_add(expr* s, expr* t, bool is_signed) {
    SASSERT(m_bv_util.is_bv(s));
    SASSERT(m_bv_util.is_bv(t));

    if (is_zero(s)) {
        return t;
    }
    if (is_zero(t)) {
        return s;
    }
    expr_ref s1(s, m()), t1(t, m());
    align_sizes(s1, t1, is_signed);
    s1 = mk_extend(1, s1, is_signed);
    t1 = mk_extend(1, t1, is_signed);
    return m_bv_util.mk_bv_add(s1, t1);
}

br_status bv2lia_rewriter_cfg::mk_add(expr* s, expr* t, expr_ref& result) {
    // TODO
    return BR_FAILED;
}

br_status bv2lia_rewriter_cfg::mk_mul(unsigned num_args, expr * const* args, expr_ref& result) {
    // TODO
    return BR_FAILED;
}

expr* bv2lia_rewriter_cfg::mk_bv_mul(expr* s, expr* t, bool is_signed) {
    SASSERT(m_bv_util.is_bv(s));
    SASSERT(m_bv_util.is_bv(t));
    if (is_zero(s)) {
        return s;
    }
    if (is_zero(t)) {
        return t;
    }    
    rational r; 
    unsigned sz;
    if (m_bv_util.is_numeral(s, r, sz) && r.is_one()) {
        return t;
    }
    if (m_bv_util.is_numeral(t, r, sz) && r.is_one()) {
        return s;
    }
    expr_ref s1(s, m()), t1(t, m());
    align_sizes(s1, t1, is_signed);
    /* TODO
    unsigned n = m_bv_util.get_bv_size(t1);    
    unsigned max_bits = m_ctx.get_max_num_bits();
    bool add_side_conds = 2*n > max_bits;
    if (n >= max_bits) {
        //
    }
    else if (2*n > max_bits) {
        s1 = mk_extend(max_bits-n, s1, is_signed);
        t1 = mk_extend(max_bits-n, t1, is_signed);        
    }
    else {
        s1 = mk_extend(n, s1, is_signed);
        t1 = mk_extend(n, t1, is_signed);
    }
    if (add_side_conds) {
        if (is_signed) {
            m_ctx.add_side_condition(m_bv_util.mk_bvsmul_no_ovfl(s1, t1));        
            m_ctx.add_side_condition(m_bv_util.mk_bvsmul_no_udfl(s1, t1));        
        }
        else {
            m_ctx.add_side_condition(m_bv_util.mk_bvumul_no_ovfl(s1, t1));        
        }
    }
    */
    return m_bv_util.mk_bv_mul(s1, t1);
}

br_status bv2lia_rewriter_cfg::mk_mul(expr* s, expr* t, expr_ref& result) {
    // TODO
    return BR_FAILED;
}

br_status bv2lia_rewriter_cfg::mk_sub(unsigned num_args, expr * const* args, expr_ref& result) {
    // TODO
    return BR_FAILED;
}

br_status bv2lia_rewriter_cfg::mk_sub(expr* s, expr* t, expr_ref& result) {
    // TODO
    return BR_FAILED;
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
