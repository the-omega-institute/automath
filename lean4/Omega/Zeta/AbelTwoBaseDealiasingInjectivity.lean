import Mathlib.NumberTheory.Real.Irrational
import Omega.Conclusion.TwoIncommensurableBasesDestroyVerticalLattice

namespace Omega.Zeta

/-- Paper label: `prop:abel-two-base-dealiasing-injectivity`. If the same phase difference is
realized as an integer vertical period for two logarithmic bases with irrational log-ratio, then
the phase difference must vanish, so the two angles agree. -/
theorem paper_abel_two_base_dealiasing_injectivity
    {b₁ b₂ γ γ' : ℝ} (hb₁ : 1 < b₁) (hb₂ : 1 < b₂)
    (hirr : Irrational (Real.log b₁ / Real.log b₂)) {m n : ℤ}
    (hbase₁ : γ - γ' = (2 * Real.pi * m) / Real.log b₁)
    (hbase₂ : γ - γ' = (2 * Real.pi * n) / Real.log b₂) :
    γ = γ' := by
  by_contra hneq
  have hperiod : ∃ T : ℝ, Omega.Conclusion.twoBaseVerticalPeriod b₁ b₂ T := by
    refine ⟨γ - γ', sub_ne_zero.mpr hneq, m, n, hbase₁, hbase₂⟩
  exact
    (Omega.Conclusion.paper_conclusion_two_incommensurable_bases_destroy_vertical_lattice
      hb₁ hb₂ hirr) hperiod

end Omega.Zeta
