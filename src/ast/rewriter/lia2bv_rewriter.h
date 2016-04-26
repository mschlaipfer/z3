/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    lia2bv_rewriter.h

Abstract:

    Partial rewriter that rewrites LIA expressions into bit-vectors

Author:

    Matthias Schlaipfer (mschlaipfer) 2016-04-21

Notes:

--*/
#ifndef LIA2BV_REWRITER_H_
#define LIA2BV_REWRITER_H_

#include"rewriter.h"

class lia2bv_rewriter_cfg : public default_rewriter_cfg {
    ast_manager                            & m_manager;
    expr_ref_vector                          m_out;
    sort_ref_vector                          m_bindings;
    bv_util                                  m_bv_util;
    arith_util                               m_arith_util;
    obj_map<expr, expr*>                   * m_lia2bv;

public:
    lia2bv_rewriter_cfg(ast_manager & m, params_ref const & p);
    ~lia2bv_rewriter_cfg();

    ast_manager & m() const { return m_manager; }
    void updt_params(params_ref const & p) {}

    void reset();

    bool pre_visit(expr * t);

    br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr);

    bool reduce_quantifier(quantifier * old_q,
                           expr * new_body,
                           expr * const * new_patterns,
                           expr * const * new_no_patterns,
                           expr_ref & result,
                           proof_ref & result_pr);

    bool reduce_var(var * t, expr_ref & result, proof_ref & result_pr);

    void set_lia2bv(obj_map<expr, expr*> * beta) { m_lia2bv = beta; };

private:
    void reduce_eq(expr * arg1, expr * arg2, unsigned sz, expr_ref & result);
    void reduce_add(expr * arg1, expr * arg2, unsigned sz, expr_ref & result);
    void reduce_mul(expr * arg1, expr * arg2, unsigned sz, expr_ref & result);
    void reduce_le(expr * arg1, expr * arg2, unsigned sz, expr_ref & result);
    void reduce_num(func_decl * arg1, expr_ref & result);

    void beta(expr * t, unsigned sz, expr_ref & result);
    void beta_sz(expr * arg1, expr * arg2, unsigned & sz);
};


struct lia2bv_rewriter : public rewriter_tpl<lia2bv_rewriter_cfg> {
    lia2bv_rewriter_cfg m_cfg;
    lia2bv_rewriter(ast_manager & m, params_ref const & p) :
        rewriter_tpl<lia2bv_rewriter_cfg>(m, false/*m.proofs_enabled()*/, m_cfg),
        m_cfg(m, p) {
    }
};

#endif

