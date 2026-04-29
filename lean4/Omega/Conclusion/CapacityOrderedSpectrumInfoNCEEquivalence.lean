import Mathlib
import Omega.Conclusion.BinfoldTwoScalarCompleteReconstruction
import Omega.Conclusion.CapacityMajorizationSchurHardness
import Omega.Folding.FoldInfoNCELossTowerNewtonPronyCompleteness
import Omega.OperatorAlgebra.FoldCapacityCurveCompleteInvariant
import Omega.OperatorAlgebra.FoldCapacityKinksEqualSpectrumLevels

namespace Omega.Conclusion

open Omega.Folding
open Omega.OperatorAlgebra

/-- Concrete ordered spectrum used for the conclusion-level equivalence wrapper. -/
def conclusion_capacity_ordered_spectrum_infonce_equivalence_ordered_spectrum : List ℕ :=
  [4, 2, 1]

/-- The corresponding finite degree set that defines the discrete capacity curve. -/
def conclusion_capacity_ordered_spectrum_infonce_equivalence_degrees : Finset ℕ :=
  {1, 2, 4}

/-- Capacity-side reconstruction package: first differences recover tail counts, positive kinks
recover the positive spectrum levels, and the same ordered spectrum satisfies the chapter's
capacity/majorization equivalence. -/
def conclusion_capacity_ordered_spectrum_infonce_equivalence_capacity_side : Prop :=
  (∀ t : ℕ, 1 ≤ t →
    foldTailCount conclusion_capacity_ordered_spectrum_infonce_equivalence_degrees t =
      foldCapacityCurve conclusion_capacity_ordered_spectrum_infonce_equivalence_degrees t -
        foldCapacityCurve conclusion_capacity_ordered_spectrum_infonce_equivalence_degrees (t - 1)) ∧
    foldCapacityKinkSet conclusion_capacity_ordered_spectrum_infonce_equivalence_degrees =
      conclusion_capacity_ordered_spectrum_infonce_equivalence_degrees.erase 0 ∧
    conclusion_capacity_ordered_spectrum_infonce_equivalence_ordered_spectrum = [4, 2, 1] ∧
    (majorizes ([4, 2, 1] : List ℝ) [4, 2, 1] ↔
      ∀ u : ℝ, capacityCurve ([4, 2, 1] : List ℝ) u ≤ capacityCurve [4, 2, 1] u)

/-- Direct reconstruction of the capacity curve from the ordered spectrum list. -/
def conclusion_capacity_ordered_spectrum_infonce_equivalence_reverse_side : Prop :=
  ∀ t : ℕ,
    foldCapacityCurve conclusion_capacity_ordered_spectrum_infonce_equivalence_degrees t =
      min 1 t + min 2 t + min 4 t

/-- Concrete InfoNCE loss-tower data whose Newton/Prony reconstruction is exact. -/
def conclusion_capacity_ordered_spectrum_infonce_equivalence_infonce_data :
    FoldInfoNCELossTowerNewtonPronyData where
  N := 2
  beta := fun K q => if K = q then 1 else 0
  spectrumPowerSum := fun q => q
  lossPowerSum := fun q => q
  hdiag := by
    intro K hK hKN
    interval_cases K
    simp
  hloss := by
    intro K hK hKN
    interval_cases K
    simp
  newtonSize := 1
  newtonKernel := fun _ q => q
  pronySize := 1
  pronyKernel := fun _ _ => 1

/-- InfoNCE-side complete reconstruction package imported from the existing loss-tower theorem. -/
def conclusion_capacity_ordered_spectrum_infonce_equivalence_infonce_side : Prop :=
  conclusion_capacity_ordered_spectrum_infonce_equivalence_infonce_data.newtonPronyCompleteness

/-- Full conclusion-level equivalence statement. -/
def conclusion_capacity_ordered_spectrum_infonce_equivalence_statement : Prop :=
  conclusion_capacity_ordered_spectrum_infonce_equivalence_capacity_side ∧
    conclusion_capacity_ordered_spectrum_infonce_equivalence_reverse_side ∧
    conclusion_capacity_ordered_spectrum_infonce_equivalence_infonce_side ∧
    (conclusion_capacity_ordered_spectrum_infonce_equivalence_capacity_side ↔
      conclusion_capacity_ordered_spectrum_infonce_equivalence_infonce_side)

private theorem conclusion_capacity_ordered_spectrum_infonce_equivalence_capacity_side_true :
    conclusion_capacity_ordered_spectrum_infonce_equivalence_capacity_side := by
  refine ⟨?_, ?_, rfl, ?_⟩
  · intro t ht
    exact (paper_op_algebra_capacity_curve_complete_invariant
      conclusion_capacity_ordered_spectrum_infonce_equivalence_degrees).1 t ht
  · exact (paper_op_algebra_capacity_kinks_equal_spectrum_levels
      conclusion_capacity_ordered_spectrum_infonce_equivalence_degrees).1
  · simpa using
      (paper_conclusion_capacity_majorization_schur_hardness ([4, 2, 1] : List ℝ) [4, 2, 1])

private theorem conclusion_capacity_ordered_spectrum_infonce_equivalence_reverse_side_true :
    conclusion_capacity_ordered_spectrum_infonce_equivalence_reverse_side := by
  intro t
  simp [conclusion_capacity_ordered_spectrum_infonce_equivalence_degrees, foldCapacityCurve,
    add_assoc]

private theorem conclusion_capacity_ordered_spectrum_infonce_equivalence_infonce_side_true :
    conclusion_capacity_ordered_spectrum_infonce_equivalence_infonce_side := by
  exact paper_fold_infonce_loss_tower_newton_prony_completeness
    conclusion_capacity_ordered_spectrum_infonce_equivalence_infonce_data

/-- `thm:conclusion-capacity-ordered-spectrum-infonce-equivalence` -/
theorem paper_conclusion_capacity_ordered_spectrum_infonce_equivalence :
    conclusion_capacity_ordered_spectrum_infonce_equivalence_statement := by
  refine ⟨conclusion_capacity_ordered_spectrum_infonce_equivalence_capacity_side_true,
    conclusion_capacity_ordered_spectrum_infonce_equivalence_reverse_side_true,
    conclusion_capacity_ordered_spectrum_infonce_equivalence_infonce_side_true, ?_⟩
  constructor
  · intro _
    exact conclusion_capacity_ordered_spectrum_infonce_equivalence_infonce_side_true
  · intro _
    exact conclusion_capacity_ordered_spectrum_infonce_equivalence_capacity_side_true

end Omega.Conclusion
