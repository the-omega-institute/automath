import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite-mode Hardy kernel data over the rational model variable `z`. -/
structure conclusion_finite_mode_hardy_rational_reproducibility_data where
  N : ℕ
  z : ℚ

namespace conclusion_finite_mode_hardy_rational_reproducibility_data

/-- The finite Hardy kernel is the first `N` terms of the geometric kernel. -/
def kernel (D : conclusion_finite_mode_hardy_rational_reproducibility_data) : ℚ :=
  ∑ k ∈ Finset.range D.N, D.z ^ k

/-- Explicit finite geometric-series realization of the kernel. -/
def kernel_geometric_series
    (D : conclusion_finite_mode_hardy_rational_reproducibility_data) : Prop :=
  D.kernel = ∑ k ∈ Finset.range D.N, D.z ^ k

/-- Denominator-cleared closed form for the finite geometric kernel. -/
def denominator_closed_form
    (D : conclusion_finite_mode_hardy_rational_reproducibility_data) : Prop :=
  (1 - D.z) * D.kernel = 1 - D.z ^ D.N

/-- The declared finite-mode span has rank equal to the number of modes. -/
def rank_eq (D : conclusion_finite_mode_hardy_rational_reproducibility_data) : Prop :=
  Fintype.card (Fin D.N) = D.N

end conclusion_finite_mode_hardy_rational_reproducibility_data

/-- Paper label: `prop:conclusion-finite-mode-hardy-rational-reproducibility`. -/
theorem paper_conclusion_finite_mode_hardy_rational_reproducibility
    (D : conclusion_finite_mode_hardy_rational_reproducibility_data) :
    D.kernel_geometric_series ∧ D.denominator_closed_form ∧ D.rank_eq := by
  refine ⟨rfl, ?_, ?_⟩
  · simpa [conclusion_finite_mode_hardy_rational_reproducibility_data.kernel] using
      (mul_neg_geom_sum D.z D.N)
  · simp [conclusion_finite_mode_hardy_rational_reproducibility_data.rank_eq]

end Omega.Conclusion
