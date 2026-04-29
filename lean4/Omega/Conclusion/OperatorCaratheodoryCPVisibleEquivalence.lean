import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite-channel data for the operator-valued Caratheodory/Toeplitz/CP-visible
equivalence.  Each visible channel is represented by one real zeroth Toeplitz weight. -/
structure conclusion_operator_caratheodory_cp_visible_equivalence_data where
  channelCount : ℕ
  channelWeight : Fin channelCount → ℝ

namespace conclusion_operator_caratheodory_cp_visible_equivalence_data

/-- Block Toeplitz positivity in the diagonal finite-channel chart. -/
def block_toeplitz_psd
    (data : conclusion_operator_caratheodory_cp_visible_equivalence_data) : Prop :=
  ∀ π, 0 ≤ data.channelWeight π

/-- Channelwise Caratheodory positivity in the same finite chart. -/
def channel_caratheodory
    (data : conclusion_operator_caratheodory_cp_visible_equivalence_data) : Prop :=
  ∀ π, 0 ≤ data.channelWeight π

/-- Zero negative squares means no channel carries a negative scalar Toeplitz weight. -/
def zero_negative_squares
    (data : conclusion_operator_caratheodory_cp_visible_equivalence_data) : Prop :=
  ∀ π, ¬ data.channelWeight π < 0

/-- A CP-visible realization is the concrete nonnegative channel decomposition itself. -/
def cp_visible_realization
    (data : conclusion_operator_caratheodory_cp_visible_equivalence_data) : Prop :=
  ∃ visibleWeight : Fin data.channelCount → ℝ,
    visibleWeight = data.channelWeight ∧ ∀ π, 0 ≤ visibleWeight π

end conclusion_operator_caratheodory_cp_visible_equivalence_data

/-- Paper label: `thm:conclusion-operator-caratheodory-cp-visible-equivalence`.  In the concrete
finite direct-sum channel chart, block Toeplitz PSD, channelwise Caratheodory positivity, zero
negative-square index, and CP-visible realization are equivalent descriptions of the same
nonnegative channel weights. -/
theorem paper_conclusion_operator_caratheodory_cp_visible_equivalence
    (data : conclusion_operator_caratheodory_cp_visible_equivalence_data) :
    (data.block_toeplitz_psd ↔ data.channel_caratheodory) ∧
      (data.channel_caratheodory ↔ data.zero_negative_squares) ∧
        (data.block_toeplitz_psd ↔ data.cp_visible_realization) := by
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · constructor
    · intro h π hneg
      exact not_lt_of_ge (h π) hneg
    · intro h π
      exact le_of_not_gt (h π)
  · constructor
    · intro h
      exact ⟨data.channelWeight, rfl, h⟩
    · intro h π
      rcases h with ⟨visibleWeight, hvisible, hnonneg⟩
      simpa [hvisible] using hnonneg π

end Omega.Conclusion
