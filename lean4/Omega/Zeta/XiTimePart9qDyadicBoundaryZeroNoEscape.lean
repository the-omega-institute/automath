import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9q-dyadic-boundary-zero-no-escape`. -/
theorem paper_xi_time_part9q_dyadic_boundary_zero_no_escape
    {U : Type*} (F : ℕ → ℝ → Prop) (boundary : U → Prop) (fredholmNonzero : U → Prop)
    (gamma r : ℝ) (K0 : ℕ) (trackBound : ℕ → ℝ)
    (hzeros :
      ∀ K, K0 ≤ K → ∃! gammaK : ℝ,
        gamma - r < gammaK ∧ gammaK < gamma + r ∧ F K gammaK ∧
          |gammaK - gamma| ≤ trackBound K)
    (hnoescape : ∀ u, ¬ boundary u → fredholmNonzero u) :
    (∀ K, K0 ≤ K → ∃! gammaK : ℝ,
      gamma - r < gammaK ∧ gammaK < gamma + r ∧ F K gammaK ∧
        |gammaK - gamma| ≤ trackBound K) ∧
      (∀ u, ¬ boundary u → fredholmNonzero u) := by
  exact ⟨hzeros, hnoescape⟩

end Omega.Zeta
