import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.POM

/-- The `q = ∞` limiting dimension corresponding to the endpoint entropy
`log(2 / √φ)`. -/
noncomputable def pom_dq_convergence_controlled_by_gq_limit : ℝ :=
  Real.log (2 / Real.sqrt Real.goldenRatio) / Real.log Real.goldenRatio

/-- The exact deviation term controlling `D_q` by the entropy gap `g_q`. -/
noncomputable def pom_dq_convergence_controlled_by_gq_deviation (gq : ℕ → ℝ) (q : ℕ) : ℝ :=
  (gq q -
      pom_dq_convergence_controlled_by_gq_limit * Real.log Real.goldenRatio) /
    (((q : ℝ) - 1) * Real.log Real.goldenRatio)

/-- Paper label: `cor:pom-Dq-convergence-controlled-by-gq`. Rewriting `h_q` from the definition of
`g_q` and substituting it into the `D_q` formula isolates the exact deviation from the limiting
dimension `D_∞`. -/
theorem paper_pom_dq_convergence_controlled_by_gq
    (hq gq Dq : ℕ → ℝ) (q : ℕ) (hq_ge : 2 ≤ q)
    (hgq : gq q = (q : ℝ) * Real.log (2 / Real.sqrt Real.goldenRatio) - hq q)
    (hDq : Dq q = (hq q / ((q : ℝ) - 1)) * (Real.log Real.goldenRatio)⁻¹) :
    pom_dq_convergence_controlled_by_gq_limit - Dq q =
      pom_dq_convergence_controlled_by_gq_deviation gq q := by
  have hlogphi_ne : Real.log Real.goldenRatio ≠ 0 := by
    exact ne_of_gt (Real.log_pos Real.one_lt_goldenRatio)
  have hq_ne : (q : ℝ) - 1 ≠ 0 := by
    have hq_gt : (1 : ℝ) < q := by
      exact_mod_cast hq_ge
    linarith
  have hlimit_mul :
      Real.log Real.goldenRatio * pom_dq_convergence_controlled_by_gq_limit =
        Real.log (2 / Real.sqrt Real.goldenRatio) := by
    unfold pom_dq_convergence_controlled_by_gq_limit
    field_simp [hlogphi_ne]
  have hlimit_mul' :
      pom_dq_convergence_controlled_by_gq_limit * Real.log Real.goldenRatio =
        Real.log (2 / Real.sqrt Real.goldenRatio) := by
    simpa [mul_comm] using hlimit_mul
  rw [hDq]
  unfold pom_dq_convergence_controlled_by_gq_deviation
  rw [hgq, hlimit_mul']
  unfold pom_dq_convergence_controlled_by_gq_limit
  field_simp [hlogphi_ne, hq_ne]
  ring_nf

end Omega.POM
