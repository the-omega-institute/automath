import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete data for the cross-resolution time renormalization defect. The wordwise defect
`Δ(w)` is the difference between the layer-`m+1` time and the pulled-back layer-`m` time. -/
structure xi_cross_resolution_time_renormalization_defect_data where
  wordCount : ℕ
  hWordCountPos : 0 < wordCount
  lengthPrev : Fin wordCount → ℝ
  lengthNext : Fin wordCount → ℝ
  defect : Fin wordCount → ℝ
  hDefect : ∀ w, defect w = lengthNext w - lengthPrev w

namespace xi_cross_resolution_time_renormalization_defect_data

/-- A distinguished base word used to normalize the defect values. -/
def xi_cross_resolution_time_renormalization_defect_anchor
    (D : xi_cross_resolution_time_renormalization_defect_data) : Fin D.wordCount :=
  ⟨0, D.hWordCountPos⟩

/-- The layerwise defect is constant in the word variable. -/
def xi_cross_resolution_time_renormalization_defect_constant_defect
    (D : xi_cross_resolution_time_renormalization_defect_data) : Prop :=
  ∃ c : ℝ, ∀ w, D.defect w = c

/-- The layerwise time function becomes affine after subtracting a single layer constant. -/
def xi_cross_resolution_time_renormalization_defect_affine_renormalization
    (D : xi_cross_resolution_time_renormalization_defect_data) : Prop :=
  ∃ c : ℝ, ∀ w, D.lengthPrev w = D.lengthNext w - c

/-- The finite set of defect values visible on the current layer. -/
noncomputable def xi_cross_resolution_time_renormalization_defect_defect_value_set
    (D : xi_cross_resolution_time_renormalization_defect_data) : Finset ℝ :=
  Finset.univ.image D.defect

/-- Minimal center rank needed to externalize the nonconstant defects. In this finite model it is
the number of distinct defect values minus one. -/
noncomputable def xi_cross_resolution_time_renormalization_defect_minimal_center_rank
    (D : xi_cross_resolution_time_renormalization_defect_data) : ℕ :=
  D.xi_cross_resolution_time_renormalization_defect_defect_value_set.card - 1

/-- Constant defect is equivalent to affine renormalization; if the defect is nonconstant, then
the finite defect-value subgroup has positive center rank. -/
noncomputable def constant_defect_iff_affine_renormalization
    (D : xi_cross_resolution_time_renormalization_defect_data) : Prop :=
  (D.xi_cross_resolution_time_renormalization_defect_constant_defect ↔
      D.xi_cross_resolution_time_renormalization_defect_affine_renormalization) ∧
    (¬ D.xi_cross_resolution_time_renormalization_defect_constant_defect →
      0 < D.xi_cross_resolution_time_renormalization_defect_minimal_center_rank)

end xi_cross_resolution_time_renormalization_defect_data

open xi_cross_resolution_time_renormalization_defect_data

/-- Paper label: `thm:xi-cross-resolution-time-renormalization-defect`. -/
theorem paper_xi_cross_resolution_time_renormalization_defect
    (D : xi_cross_resolution_time_renormalization_defect_data) :
    D.constant_defect_iff_affine_renormalization := by
  refine ⟨?_, ?_⟩
  · constructor
    · intro hconst
      rcases hconst with ⟨c, hc⟩
      refine ⟨c, ?_⟩
      intro w
      have hdef := D.hDefect w
      have hw : D.defect w = c := hc w
      linarith
    · intro hAffine
      rcases hAffine with ⟨c, hc⟩
      refine ⟨c, ?_⟩
      intro w
      have hdef := D.hDefect w
      have hw : D.lengthPrev w = D.lengthNext w - c := hc w
      linarith
  · intro hNonconstant
    have hWitness :
        ∃ w, D.defect w ≠
          D.defect D.xi_cross_resolution_time_renormalization_defect_anchor := by
      by_contra hNoWitness
      apply hNonconstant
      refine ⟨D.defect D.xi_cross_resolution_time_renormalization_defect_anchor, ?_⟩
      intro w
      by_contra hw
      exact hNoWitness ⟨w, hw⟩
    rcases hWitness with ⟨w, hw⟩
    have hAnchorMem :
        D.defect D.xi_cross_resolution_time_renormalization_defect_anchor ∈
          D.xi_cross_resolution_time_renormalization_defect_defect_value_set := by
      refine Finset.mem_image.mpr ?_
      exact ⟨D.xi_cross_resolution_time_renormalization_defect_anchor, by simp, rfl⟩
    have hWitnessMem :
        D.defect w ∈ D.xi_cross_resolution_time_renormalization_defect_defect_value_set := by
      refine Finset.mem_image.mpr ?_
      exact ⟨w, by simp, rfl⟩
    have hCard :
        1 <
          D.xi_cross_resolution_time_renormalization_defect_defect_value_set.card := by
      exact Finset.one_lt_card.mpr
        ⟨D.defect D.xi_cross_resolution_time_renormalization_defect_anchor, hAnchorMem,
          D.defect w, hWitnessMem, hw.symm⟩
    change 0 <
      D.xi_cross_resolution_time_renormalization_defect_defect_value_set.card - 1
    exact Nat.sub_pos_of_lt hCard

end
end Omega.Zeta
