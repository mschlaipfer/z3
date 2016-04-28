/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    bv2lia_rewriter.h

Abstract:

    Rewriter that rewrites bit-vectors into LIA expressions.

Author:

    Matthias Schlaipfer (mschlaipfer) 2016-04-18

Notes:

--*/
#ifndef BV2LIA_REWRITER_H_
#define BV2LIA_REWRITER_H_

#include"rewriter.h"

class bv2lia_rewriter_cfg : public default_rewriter_cfg {
    ast_manager                            & m_manager;
    expr_ref_vector                          m_out;
    sort_ref_vector                          m_bindings;
    bv_util                                  m_bv_util;
    arith_util                               m_arith_util;
    obj_map<expr, expr*>                     m_bv2lia;
    obj_map<func_decl, func_decl*>           m_bvop2uf;
    obj_map<expr, expr*>                     m_lia2bv; // beta in [Griggio '11]
    obj_map<func_decl, func_decl*>           m_uf2bvop;
    expr_ref_vector                          m_side_conditions;
    expr_ref_vector                          m_stack;
    obj_map<expr, unsigned>                  m_bv2sz;
    sort                                   * int_sort;
    func_decl                              * f_mul;

public:
    bv2lia_rewriter_cfg(ast_manager & m, params_ref const & p);
    ~bv2lia_rewriter_cfg();

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

    obj_map<expr, expr*> const& get_lia2bv() const { return m_lia2bv; };

    obj_map<func_decl, func_decl*> const& get_uf2bvop() const { return m_uf2bvop; };

    expr_ref_vector const& get_side_conditions() const { return m_side_conditions; };

private:
    void reduce_eq(expr * arg1, expr * arg2, expr_ref & result);
    void reduce_concat(expr * arg1, expr * arg2, expr_ref & result);
    void reduce_badd(expr * arg1, expr * arg2, expr_ref & result);
    void reduce_mul(func_decl * f, expr * arg1, expr * arg2, expr_ref & result);
    void reduce_uleq(expr * arg1, expr * arg2, expr_ref & result);
    void reduce_bv_num(func_decl * arg1, expr_ref & result);
    /*
    br_status mk_ite(expr* c, expr* s, expr* t, expr_ref& result);
    br_status mk_le(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_lt(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_ge(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_gt(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_idiv(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_mod(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_rem(expr * arg1, expr * arg2, expr_ref & result);   
    br_status mk_add(unsigned num_args, expr * const * args, expr_ref & result);     
    br_status mk_mul(unsigned num_args, expr * const * args, expr_ref & result); 
    br_status mk_sub(unsigned num_args, expr * const * args, expr_ref & result); 
    br_status mk_add(expr* s, expr* t, expr_ref& result);
    br_status mk_mul(expr* s, expr* t, expr_ref& result);
    br_status mk_sub(expr* s, expr* t, expr_ref& result);
    br_status mk_uminus(expr* e, expr_ref & result); 
    */

    expr*     fresh_var(expr* t);
    expr*     fresh_var(expr* t, unsigned &sz);
    expr*     fresh_var(rational const & upper);

    func_decl* fresh_func(func_decl* f);
    
    expr*     add_side_condition(expr* t, rational const & upper);
};


struct bv2lia_rewriter : public rewriter_tpl<bv2lia_rewriter_cfg> {
    bv2lia_rewriter_cfg m_cfg;
    bv2lia_rewriter(ast_manager & m, params_ref const & p) :
        rewriter_tpl<bv2lia_rewriter_cfg>(m, m.proofs_enabled(), m_cfg),
        m_cfg(m, p) {
    }
};

#endif

