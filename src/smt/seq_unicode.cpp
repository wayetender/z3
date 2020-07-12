/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    seq_unicode.cpp

Abstract:

    Solver for unicode characters

Author:

    Nikolaj Bjorner (nbjorner) 2020-5-16
    Max Levatich 2020-7-1

--*/

#include "ast/ast_pp.h"
#include "smt/seq_unicode.h"
#include "smt/smt_context.h"
#include "smt/smt_arith_value.h"
#include "util/trail.h"

#define NICE_MIN 97
#define NICE_MAX 122

namespace smt {

    void seq_unicode::nc_functor::linearize() { 
        m_assumptions.reset();
        m_literals.reset(); 
        m_eqs.reset();
        for (auto* d : m_deps) 
            dm.linearize(d, m_assumptions);
        for (seq_assumption const& a : m_assumptions) {
            if (a.lit != null_literal) {
                m_literals.push_back(a.lit);
            }
            if (a.n1 != nullptr) {
                m_eqs.push_back(enode_pair(a.n1, a.n2));
            }
        }
    }


    seq_unicode::seq_unicode(theory& th, seq_dependency_manager& dm):
        th(th),
        m(th.get_manager()),
        dm(dm),
        seq(m),
        m_qhead(0),
        m_nc_functor(dm),
        m_var_value_hash(*this),
        m_var_value_eq(*this),
        m_var_value_table(DEFAULT_HASHTABLE_INITIAL_CAPACITY, m_var_value_hash, m_var_value_eq),
        m_uses_to_code(false)
    {}

    // <= atomic constraints on characters
    edge_id seq_unicode::assign_le(theory_var v1, theory_var v2, dependency* dep) {
        dl.init_var(v1);
        dl.init_var(v2);
        TRACE("seq", tout << mk_pp(th.get_expr(v1), m) << " <= " << mk_pp(th.get_expr(v2), m) << "\n";);
        return add_edge(v1, v2, 0, dep);
    }

    // < atomic constraint on characters
    edge_id seq_unicode::assign_lt(theory_var v1, theory_var v2, dependency* dep) {
        dl.init_var(v1);
        dl.init_var(v2);
        TRACE("seq", tout << mk_pp(th.get_expr(v1), m) << " < " << mk_pp(th.get_expr(v2), m) << "\n";);
        return add_edge(v1, v2, -1, dep);
    }

    edge_id seq_unicode::add_edge(theory_var v1, theory_var v2, int diff, dependency* dep) {
        ctx().push_trail(push_back_vector<context, svector<theory_var>>(m_asserted_edges));
        edge_id new_edge = dl.add_edge(v2, v1, s_integer(diff), dep);
        m_asserted_edges.push_back(new_edge);
        return new_edge;
    }

    literal seq_unicode::mk_literal(expr* e) {
        expr_ref _e(e, m);
        th.ensure_enode(e);
        return ctx().get_literal(e);
    }

    // = on characters
    void seq_unicode::new_eq_eh(theory_var v1, theory_var v2, dependency* dep) {
        assign_le(v1, v2, dep);
        assign_le(v2, v1, dep);
    }

    // != on characters
    void seq_unicode::new_diseq_eh(theory_var v1, theory_var v2) {
        dl.init_var(v1);
        dl.init_var(v2);
#if 0
        enforce_diseq(v1, v2);
#else
        m_diseqs.push_back(std::make_pair(v1, v2));
#endif
    }

    void seq_unicode::enforce_diseq(theory_var v1, theory_var v2) {
        expr* e1 = th.get_expr(v1);
        expr* e2 = th.get_expr(v2);
        literal eq = th.mk_eq(e1, e2, false);
        literal le = mk_literal(seq.mk_le(e1, e2));
        literal ge = mk_literal(seq.mk_le(e2, e1));
        add_axiom(~le, ~ge, eq);
    }

    bool seq_unicode::try_bound(theory_var v, unsigned min, unsigned max) {

        local_scope sc(*this);
        dl.init_var(v);
        theory_var v0 = ensure0();
        // v0 - v <= - min
        // v - v0 <= max
        bool is_sat = 
            dl.enable_edge(dl.add_edge(v, v0, s_integer(-1 * min), nullptr))
            && dl.enable_edge(dl.add_edge(v0, v, s_integer(max), nullptr));
        if (is_sat) 
            dl.set_to_zero(v0);
        return is_sat;
    }

    bool seq_unicode::try_assignment(theory_var v, unsigned ch) {
        return try_bound(v, ch, ch);
    }

    void seq_unicode::try_make_nice(svector<theory_var> const& char_vars) {

        // Try for each character
        unsigned i = 0;
        for (auto v : char_vars) {

            // Skip character constants, since they can't be changed
            if (seq.is_const_char(th.get_expr(v))) 
                continue;

            // Check if the value is already nice
            int val = get_value(v);
            if (NICE_MIN <= val && val <= NICE_MAX)
                continue;
        
            // Try assigning the variable to a nice value
            if (try_bound(v, NICE_MIN, NICE_MAX) && 
                try_assignment(v, NICE_MIN + (i % (NICE_MAX - NICE_MIN + 1)))) {
                i++;
            }
        }
    }


    bool seq_unicode::enforce_char_range(svector<theory_var> const& char_vars) {

        // Continue checking until convergence or inconsistency
        bool done = false;
        while (!done) {
            done = true;

            // Iterate over variables and ensure that their values are in 0 <= v <= zstring::max_char()
            for (auto v : char_vars) {
                int val = get_value(v);
                if (val < 0) {
                    done = false;

                    // v0 = 0
                    theory_var v0 = ensure0();

                    // Add constraint on v and check consistency
                    propagate(assign_le(v0, v, nullptr));
                    if (ctx().inconsistent()) return false;
                }
                if (val > static_cast<int>(zstring::max_char())) {
                    done = false;

                    // v_maxchar = zstring::max_char()
                    theory_var v_maxchar = ensure_maxchar();

                    // Add constraint on v and check consistency
                    propagate(assign_le(v, v_maxchar, nullptr));
                    if (ctx().inconsistent()) return false;
                }
            }
        }
        return true;
    }

    void seq_unicode::set_uses_to_code() {
        if (!m_uses_to_code) {
            ctx().push_trail(value_trail<smt::context, bool>(m_uses_to_code));
            m_uses_to_code = true;
        }
    }


    /**
     * Enforce: 
     *    to_code(s) = v => s = unit(@char(v))
     */
    bool seq_unicode::enforce_char_codes(svector<theory_var> const& char_vars) {
        bool success = true;
        if (!m_uses_to_code)
            return success;
        arith_util a(m);
        arith_value avalue(m);
        avalue.init(&ctx());
        rational v;

        for (enode* n : ctx().enodes()) {
            app* to_code = n->get_owner();
            if (!seq.str.is_to_code(to_code)) 
                continue;
            if (!avalue.get_value(to_code, v))
                continue;
            if (v.is_neg() || !v.is_unsigned() || v.get_unsigned() > zstring::max_char())
                continue;
            enode* s = n->get_arg(0);
            app_ref ch(seq.str.mk_unit(seq.str.mk_char(v.get_unsigned())), m);
            enode* s2 = th.ensure_enode(ch);
            if (s->get_root() != s2->get_root()) {
                add_axiom(~th.mk_eq(to_code, a.mk_int(v), false), th.mk_eq(s->get_owner(), ch, false));
                success = false;
                break;
            }
        }

        // If a constraint was added without being propagated, we can't be finished yet
        return success;
    }

    bool seq_unicode::final_check() {

        // Get character variables
        svector<theory_var> char_vars;
        for (unsigned v = 0; v < th.get_num_vars(); ++v) 
            if (seq.is_char(th.get_expr(v)) && th.get_enode(v)->is_root()) 
                char_vars.push_back(v);        

        // Shift assignments on variables, so that they are "nice" (have values 'a', 'b', ...)
//        try_make_nice(char_vars);

        // Validate that all variables must be in 0 <= v <= zstring::max_char()
        if (!enforce_char_range(char_vars)) 
            return false;

        // Make sure str.to_code(unit(v)) = val for all character variables
        if (!enforce_char_codes(char_vars)) 
            return false;

        if (!check_diseqs())
            return false;
        
        // Ensure that equal characters are known to be equal to congruences.
        if (!assume_eqs(char_vars)) 
            return false;

        TRACE("seq", display(tout););
        // If all checks pass, we're done
        return true;
    }

    bool seq_unicode::check_diseqs() {
        unsigned eqs = 0;
        for (auto p : m_diseqs) {
            theory_var v1 = p.first;
            theory_var v2 = p.second;
            if (dl.get_assignment(v1).get_int() == dl.get_assignment(v2).get_int()) {
                enforce_diseq(v1, v2);
                ++eqs;
            }
        }
        return eqs == 0;
    }

    bool seq_unicode::assume_eqs(svector<theory_var> const& vars) {
        m_var_value_table.reset();
        bool success = true;
        for (theory_var v : vars) {
            theory_var w = m_var_value_table.insert_if_not_there(v);
            if (w != v && th.assume_eq(th.get_enode(v), th.get_enode(w))) {
                TRACE("seq", tout << "assume v" << v << " == v" << w << "\n";);
                success = false;
            }            
        }
        return success;
    }

    void seq_unicode::enforce_is_value(app* n, unsigned ch) {
        enode* e = th.ensure_enode(n);
        theory_var v = e->get_th_var(th.get_id());
        if (v == null_theory_var)
            return;
        enforce_tv_is_value(v, ch);
    }

    void seq_unicode::enforce_tv_is_value(theory_var v, unsigned ch) {
        dl.init_var(v);
        if (ch == 0) {
            dl.set_to_zero(v);
        }
        else {
            theory_var v0 = ensure0();
            add_edge(v, v0, ch, nullptr);  // v - v0 <= ch
            add_edge(v0, v, -static_cast<int>(ch), nullptr);  // v0 - v <= -ch
        }
    }

    theory_var seq_unicode::ensure0() {
        expr_ref ch(seq.str.mk_char(0), m);
        enode* n = th.ensure_enode(ch);
        theory_var v0 = n->get_th_var(th.get_id());
        dl.init_var(v0);
        dl.set_to_zero(v0);
        return v0;
    }

    theory_var seq_unicode::ensure_maxchar() {
        expr_ref ch(seq.str.mk_char(zstring::max_char()), m);
        enode* n = th.ensure_enode(ch);
        theory_var v_maxchar = n->get_th_var(th.get_id());
        dl.init_var(v_maxchar);
        return v_maxchar;
    }

    void seq_unicode::propagate() {
        ctx().push_trail(value_trail<smt::context, unsigned>(m_qhead));
        for (; m_qhead < m_asserted_edges.size() && !ctx().inconsistent(); ++m_qhead) {
            propagate(m_asserted_edges[m_qhead]);
        }
    }

    void seq_unicode::propagate(edge_id edge) {
        if (dl.enable_edge(edge))
            return;
        m_nc_functor.reset();
        dl.traverse_neg_cycle2(false, m_nc_functor);
        m_nc_functor.linearize();
        auto const & lits = m_nc_functor.get_lits();
        auto const & eqs = m_nc_functor.get_eqs();
        vector<parameter> params;
        if (m.proofs_enabled()) {
            params.push_back(parameter(symbol("farkas")));
            for (unsigned i = 0; i <= lits.size() + eqs.size(); ++i) {
                params.push_back(parameter(rational(1)));
            }
        }
        TRACE("seq", tout << "conflict " << lits << "\n";);
        ctx().set_conflict(
            ctx().mk_justification(
                ext_theory_conflict_justification(
                    th.get_id(), ctx().get_region(),
                    lits.size(), lits.c_ptr(),
                    eqs.size(), eqs.c_ptr(),
                    params.size(), params.c_ptr())));
        SASSERT(ctx().inconsistent());
    }

    unsigned seq_unicode::get_value(theory_var v) {
        dl.init_var(v);
        TRACE("seq", tout << "get value: " << v << " " << mk_pp(th.get_expr(v), m) << " " << dl.get_assignment(v).get_int() << "\n";);
        return dl.get_assignment(v).get_int();
    }

    void seq_unicode::push_scope() {
        dl.push();
        m_diseqs_lim.push_back(m_diseqs.size());
    }

    void seq_unicode::pop_scope(unsigned n) {
        dl.pop(n);
        m_diseqs.shrink(m_diseqs_lim[m_diseqs_lim.size() - n]);
        m_diseqs_lim.shrink(m_diseqs_lim.size() - n);
    }


}
