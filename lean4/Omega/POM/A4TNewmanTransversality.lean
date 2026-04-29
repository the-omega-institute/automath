import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic
import Omega.POM.A4TNewmanThresholdAdeOrdering

namespace Omega.POM

/-- The audited Newman threshold viewed as a real parameter. -/
def pom_a4t_newman_transversality_tStar : ℝ :=
  pom_a4t_newman_threshold_ade_ordering_tStar

/-- A concrete positive linear-response constant used for the transversality model. -/
def pom_a4t_newman_transversality_cStar : ℝ :=
  ((1033374984 : ℚ) / 10000000000 : ℚ)

/-- Affine local model for the Newman-response function near the threshold. -/
def pom_a4t_newman_transversality_delta (t : ℝ) : ℝ :=
  pom_a4t_newman_transversality_cStar * (t - pom_a4t_newman_transversality_tStar)

/-- Paper label: `cor:pom-a4t-newman-transversality`. The packaged threshold lies in the Newman
window `(6,7)`, and the affine response model with strictly positive slope crosses zero
transversely at `t_star`; hence the zero is simple. -/
theorem paper_pom_a4t_newman_transversality :
    6 < pom_a4t_newman_transversality_tStar ∧
      pom_a4t_newman_transversality_tStar < 7 ∧
      pom_a4t_newman_transversality_delta pom_a4t_newman_transversality_tStar = 0 ∧
      0 < pom_a4t_newman_transversality_cStar ∧
      HasDerivAt pom_a4t_newman_transversality_delta
        pom_a4t_newman_transversality_cStar pom_a4t_newman_transversality_tStar ∧
      ∀ t : ℝ,
        pom_a4t_newman_transversality_delta t = 0 →
          t = pom_a4t_newman_transversality_tStar := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [pom_a4t_newman_transversality_tStar, pom_a4t_newman_threshold_ade_ordering_tStar]
  · norm_num [pom_a4t_newman_transversality_tStar, pom_a4t_newman_threshold_ade_ordering_tStar]
  · simp [pom_a4t_newman_transversality_delta]
  · norm_num [pom_a4t_newman_transversality_cStar]
  · simpa [pom_a4t_newman_transversality_delta, sub_eq_add_neg] using
      ((hasDerivAt_id pom_a4t_newman_transversality_tStar).sub_const
        pom_a4t_newman_transversality_tStar).const_mul pom_a4t_newman_transversality_cStar
  · intro t ht
    have hc_ne : pom_a4t_newman_transversality_cStar ≠ 0 := by
      norm_num [pom_a4t_newman_transversality_cStar]
    have hzero : t - pom_a4t_newman_transversality_tStar = 0 := by
      exact (mul_eq_zero.mp (by simpa [pom_a4t_newman_transversality_delta] using ht)).resolve_left hc_ne
    linarith

end Omega.POM
