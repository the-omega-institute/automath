import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-leyang-simple-root-algebraic-jet-closure`.  If the root value is
algebraic and each implicit-differentiation step recovers the next jet from all earlier jets, then
every jet is algebraic. -/
theorem paper_xi_leyang_simple_root_algebraic_jet_closure (jetAlgebraic : ℕ → Prop)
    (h0 : jetAlgebraic 0)
    (hstep : ∀ n, (∀ k, k ≤ n → jetAlgebraic k) → jetAlgebraic (n + 1)) :
    ∀ n, jetAlgebraic n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => exact h0
      | succ m =>
          exact hstep m (by
            intro k hk
            exact ih k (Nat.lt_succ_of_le hk))

end Omega.Zeta
