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

    if (m().is_eq(f)) {
        SASSERT(num == 2);
        if (m_arith_util.is_int(args[0])) {
            reduce_eq(args[0], args[1], result);
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

    if (f->get_family_id() == m_arith_util.get_family_id()) {
        switch (f->get_decl_kind()) {
        case OP_NUM:
            SASSERT(num == 0);
            reduce_num(f, result);
            //return BR_DONE;
            return BR_FAILED;
        case OP_ADD:
            // TODO support varargs?
            reduce_add(args[0], args[1], result);
            return BR_DONE;
        /*
        case OP_BMUL:
            if (!m_blast_mul)
                return BR_FAILED;
            reduce_mul(num, args, result);
            return BR_DONE;
        */
        case OP_LE:
            SASSERT(num == 2);
            reduce_le(args[0], args[1], 8, result);
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

// TODO
void lia2bv_rewriter_cfg::reduce_eq(expr * arg1, expr * arg2, expr_ref & result) {
}

// TODO
void lia2bv_rewriter_cfg::reduce_add(expr * arg1, expr * arg2, expr_ref & result) {
}

// TODO
void lia2bv_rewriter_cfg::reduce_le(expr * arg1, expr * arg2, unsigned sz, expr_ref & result) {
    TRACE("lia2bv", tout << "reduce_le: " << mk_pp(arg1, m()) << ", " << mk_pp(arg2, m()) << std::endl;);

    TRACE("lia2bv", tout << "get_lia2bv:" << std::endl;
    for (obj_map<expr, expr*>::iterator it = m_lia2bv->begin(); it != m_lia2bv->end(); ++it) {
        tout << mk_pp(it->m_key, m()) << " -> " << mk_ismt2_pp(it->m_value, m()) << std::endl;
    }
    );
    expr_ref bv_arg1(m());
    beta(arg1, sz, bv_arg1);

    expr_ref bv_arg2(m());
    beta(arg2, sz, bv_arg2);

    TRACE("lia2bv", tout << "reduce_le: " << mk_pp(bv_arg1, m()) << ", " << mk_pp(bv_arg2, m()) << std::endl;);
    result = m_bv_util.mk_ule(bv_arg1, bv_arg2);
    TRACE("lia2bv", tout << "reduce_le: " << mk_pp(result, m()) << std::endl;);
    //SASSERT(m_bv_util.is_bv(result));
}

void lia2bv_rewriter_cfg::reduce_num(func_decl * arg1, expr_ref & result) {
    //TRACE("lia2bv", tout << "reduce_num: " << arg1->get_parameter(0) << std::endl;);
    //rational v  = arg1->get_parameter(0).get_rational();
    //result = m_bv_util.mk_(v, true);
    //TRACE("lia2bv", tout << "result: " << mk_pp(result, m()) << std::endl;);
}

bool lia2bv_rewriter_cfg::pre_visit(expr * t)
{
    TRACE("lia2bv_rw_q", tout << "pre_visit: " << mk_ismt2_pp(t, m()) << std::endl;);

    if (is_quantifier(t)) {
        quantifier * q = to_quantifier(t);
        TRACE("lia2bv_rw_q", tout << "pre_visit quantifier [" << q->get_id() << "]: " << mk_ismt2_pp(q->get_expr(), m()) << std::endl;);
        sort_ref_vector new_bindings(m_manager);
        for (unsigned i = 0; i < q->get_num_decls(); i++)
            new_bindings.push_back(q->get_decl_sort(i));
        SASSERT(new_bindings.size() == q->get_num_decls());
        m_bindings.append(new_bindings);
    }
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
