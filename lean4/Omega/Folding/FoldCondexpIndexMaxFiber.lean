import Omega.Folding.MaxFiber
import Omega.OperatorAlgebra.RenyiFlatnessSupEqualsLogIndex
import Omega.POM.HiddenBitWatataniIndexElement

namespace Omega

open Omega.OperatorAlgebra

/-- Paper label: `prop:fold-condexp-index-maxfiber`. -/
theorem paper_fold_condexp_index_maxfiber (m : ℕ) :
    (∃ x : Omega.X m, Omega.X.fiberMultiplicity x = Omega.X.maxFiberMultiplicity m) ∧
      (∀ x : Omega.X m, Omega.X.fiberMultiplicity x ≤ Omega.X.maxFiberMultiplicity m) ∧
      0 < Omega.X.maxFiberMultiplicity m ∧
      sSup (Set.range
        (Omega.OperatorAlgebra.foldFiberRenyiFlatness (Omega.Fold : Omega.Word m → Omega.X m))) =
        Real.log (Omega.X.maxFiberMultiplicity m) := by
  rcases Omega.X.paper_fold_condexp_index_maxfiber_support m with ⟨hach, hcap, hpos⟩
  refine ⟨hach, hcap, hpos, ?_⟩
  refine Omega.OperatorAlgebra.paper_op_algebra_renyi_flatness_sup_equals_log_index
    (Omega.Fold : Omega.Word m → Omega.X m) (Omega.X.maxFiberMultiplicity m) ?_ ?_
  · intro ω
    calc
      Fintype.card
          (Omega.OperatorAlgebra.FoldJonesBasicConstructionDirectsum.foldFiber
            (Omega.Fold : Omega.Word m → Omega.X m)
            ((Omega.Fold : Omega.Word m → Omega.X m) ω)) =
          Omega.X.fiberMultiplicity (Omega.Fold ω) := by
            exact Omega.POM.pom_hiddenbit_watatani_index_element_foldFiber_card_eq_fiberMultiplicity
              m (Omega.Fold ω)
      _ ≤ Omega.X.maxFiberMultiplicity m := hcap (Omega.Fold ω)
  · rcases hach with ⟨x, hx⟩
    refine ⟨Omega.X.choosePreimage x, ?_⟩
    calc
      Fintype.card
          (Omega.OperatorAlgebra.FoldJonesBasicConstructionDirectsum.foldFiber
            (Omega.Fold : Omega.Word m → Omega.X m)
            ((Omega.Fold : Omega.Word m → Omega.X m) (Omega.X.choosePreimage x))) =
          Omega.X.fiberMultiplicity (Omega.Fold (Omega.X.choosePreimage x)) := by
            exact Omega.POM.pom_hiddenbit_watatani_index_element_foldFiber_card_eq_fiberMultiplicity
              m (Omega.Fold (Omega.X.choosePreimage x))
      _ = Omega.X.maxFiberMultiplicity m := by simp [hx]

end Omega
