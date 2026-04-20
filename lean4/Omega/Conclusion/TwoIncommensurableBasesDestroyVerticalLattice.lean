import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

namespace Omega.Conclusion

/-- A common nonzero pure-imaginary period for the two logarithmic scales `L₁` and `L₂`,
written in the standard vertical-lattice form coming from each base separately. -/
def twoBaseVerticalPeriod (L₁ L₂ T : ℝ) : Prop :=
  T ≠ 0 ∧ ∃ m n : ℤ,
    T = (2 * Real.pi * m) / Real.log L₁ ∧
      T = (2 * Real.pi * n) / Real.log L₂

/-- Two incommensurable logarithmic bases cannot share a nonzero vertical lattice period.
    thm:conclusion-two-incommensurable-bases-destroy-vertical-lattice -/
theorem paper_conclusion_two_incommensurable_bases_destroy_vertical_lattice
    {L₁ L₂ : ℝ} (hL₁ : 1 < L₁) (hL₂ : 1 < L₂)
    (hincomm : Irrational (Real.log L₁ / Real.log L₂)) :
    ¬ ∃ T : ℝ, twoBaseVerticalPeriod L₁ L₂ T := by
  intro h
  rcases h with ⟨T, hT0, m, n, hTm, hTn⟩
  have hlog₁_pos : 0 < Real.log L₁ := Real.log_pos hL₁
  have hlog₂_pos : 0 < Real.log L₂ := Real.log_pos hL₂
  have hlog₁ : Real.log L₁ ≠ 0 := hlog₁_pos.ne'
  have hlog₂ : Real.log L₂ ≠ 0 := hlog₂_pos.ne'
  have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hm : m ≠ 0 := by
    intro hm
    have : T = 0 := by
      rw [hTm, hm]
      simp
    exact hT0 this
  have hn : n ≠ 0 := by
    intro hn
    have : T = 0 := by
      rw [hTn, hn]
      simp
    exact hT0 this
  have hEq : (2 * Real.pi * (m : ℝ)) / Real.log L₁ = (2 * Real.pi * (n : ℝ)) / Real.log L₂ := by
    rw [← hTm, hTn]
  have hcross : (m : ℝ) * Real.log L₂ = (n : ℝ) * Real.log L₁ := by
    field_simp [hlog₁, hlog₂, htwoPi] at hEq
    linarith
  have hn_real : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hratio : Real.log L₁ / Real.log L₂ = (m : ℝ) / (n : ℝ) := by
    field_simp [hlog₂, hn_real]
    nlinarith [hcross]
  exact (irrational_iff_ne_rational _).mp hincomm m n hn <| by
    simpa using hratio

end Omega.Conclusion
