import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

namespace Omega.Conclusion

open Filter
open scoped Topology

/-- Concrete sequence data for zero profile versus eventual zero defect. -/
structure conclusion_comoving_zero_profile_zero_defect_equivalence_data where
  defectCount : ℕ → ℕ
  l1Norm : ℕ → ℝ
  linfNorm : ℕ → ℝ
  l1LowerBound : ℝ
  linfLowerBound : ℝ
  l1LowerBound_pos : 0 < l1LowerBound
  linfLowerBound_pos : 0 < linfLowerBound
  l1_zero_of_zero_defect : ∀ ν : ℕ, defectCount ν = 0 → l1Norm ν = 0
  linf_zero_of_zero_defect : ∀ ν : ℕ, defectCount ν = 0 → linfNorm ν = 0
  l1_lower_of_nonzero_defect : ∀ ν : ℕ, defectCount ν ≠ 0 → l1LowerBound ≤ l1Norm ν
  linf_lower_of_nonzero_defect : ∀ ν : ℕ, defectCount ν ≠ 0 → linfLowerBound ≤ linfNorm ν

/-- Both norm profiles vanish exactly when the defect count is eventually zero. -/
def conclusion_comoving_zero_profile_zero_defect_equivalence_statement
    (D : conclusion_comoving_zero_profile_zero_defect_equivalence_data) : Prop :=
  (Tendsto D.l1Norm atTop (𝓝 0) ∧ Tendsto D.linfNorm atTop (𝓝 0)) ↔
    ∀ᶠ ν in atTop, D.defectCount ν = 0

lemma conclusion_comoving_zero_profile_zero_defect_equivalence_eventual_zero_to_tendsto
    (D : conclusion_comoving_zero_profile_zero_defect_equivalence_data)
    (hzero : ∀ᶠ ν in atTop, D.defectCount ν = 0) :
    Tendsto D.l1Norm atTop (𝓝 0) ∧ Tendsto D.linfNorm atTop (𝓝 0) := by
  refine ⟨?_, ?_⟩
  · rcases Filter.eventually_atTop.1 hzero with ⟨N, hN⟩
    exact tendsto_atTop_of_eventually_const (i₀ := N) fun ν hν =>
      D.l1_zero_of_zero_defect ν (hN ν hν)
  · rcases Filter.eventually_atTop.1 hzero with ⟨N, hN⟩
    exact tendsto_atTop_of_eventually_const (i₀ := N) fun ν hν =>
      D.linf_zero_of_zero_defect ν (hN ν hν)

lemma conclusion_comoving_zero_profile_zero_defect_equivalence_tendsto_to_eventual_zero
    (D : conclusion_comoving_zero_profile_zero_defect_equivalence_data)
    (hl1 : Tendsto D.l1Norm atTop (𝓝 0)) :
    ∀ᶠ ν in atTop, D.defectCount ν = 0 := by
  have hsmall : ∀ᶠ ν in atTop, D.l1Norm ν < D.l1LowerBound :=
    hl1.eventually (isOpen_Iio.mem_nhds D.l1LowerBound_pos)
  filter_upwards [hsmall] with ν hνsmall
  by_contra hν
  exact not_le_of_gt hνsmall (D.l1_lower_of_nonzero_defect ν hν)

/-- Paper label: `cor:conclusion-comoving-zero-profile-zero-defect-equivalence`. -/
theorem paper_conclusion_comoving_zero_profile_zero_defect_equivalence
    (D : conclusion_comoving_zero_profile_zero_defect_equivalence_data) :
    conclusion_comoving_zero_profile_zero_defect_equivalence_statement D := by
  constructor
  · intro hnorms
    exact conclusion_comoving_zero_profile_zero_defect_equivalence_tendsto_to_eventual_zero D
      hnorms.1
  · intro hzero
    exact conclusion_comoving_zero_profile_zero_defect_equivalence_eventual_zero_to_tendsto D hzero

end Omega.Conclusion
