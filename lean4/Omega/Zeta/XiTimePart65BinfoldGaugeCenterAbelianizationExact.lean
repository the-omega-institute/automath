import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldGaugeGroupStructure

namespace Omega.Zeta

open scoped BigOperators

/-- The fold-gauge center only receives a nontrivial `ℤ/2ℤ` contribution from the fibers of
multiplicity exactly `2`, while the abelianization receives one from every fiber of multiplicity
at least `2`. Counting those fibers converts the componentwise order formulas into powers of `2`.
    thm:xi-time-part65-binfold-gauge-center-abelianization-exact -/
theorem paper_xi_time_part65_binfold_gauge_center_abelianization_exact {m : Nat}
    (fiber : Fin m → Nat) :
    let n2 := (Finset.univ.filter fun w => fiber w = 2).card
    let nge2 := (Finset.univ.filter fun w => 2 <= fiber w).card
    Omega.OperatorAlgebra.foldGaugeCenterOrder fiber = 2 ^ n2 ∧
      Omega.OperatorAlgebra.foldGaugeAbelianizationOrder fiber = 2 ^ nge2 := by
  dsimp
  constructor
  · calc
      Omega.OperatorAlgebra.foldGaugeCenterOrder fiber
          = ∏ w ∈ Finset.univ, if fiber w = 2 then 2 else 1 := by
              simp [Omega.OperatorAlgebra.foldGaugeCenterOrder,
                Omega.OperatorAlgebra.foldGaugeCenterComponentOrder]
      _ = ∏ w ∈ Finset.univ.filter (fun w => fiber w = 2), (2 : Nat) := by
            rw [Finset.prod_filter]
      _ = 2 ^ (Finset.univ.filter (fun w => fiber w = 2)).card := by
            simp
  · calc
      Omega.OperatorAlgebra.foldGaugeAbelianizationOrder fiber
          = ∏ w ∈ Finset.univ, if 2 ≤ fiber w then 2 else 1 := by
              unfold Omega.OperatorAlgebra.foldGaugeAbelianizationOrder
              refine Finset.prod_congr rfl ?_
              intro w hw
              by_cases hge : 2 ≤ fiber w
              · have hle : ¬ fiber w ≤ 1 := by omega
                simp [Omega.OperatorAlgebra.foldGaugeAbelianizationComponentOrder, hge, hle]
              · have hle : fiber w ≤ 1 := by omega
                simp [Omega.OperatorAlgebra.foldGaugeAbelianizationComponentOrder, hge, hle]
      _ = ∏ w ∈ Finset.univ.filter (fun w => 2 ≤ fiber w), (2 : Nat) := by
            rw [Finset.prod_filter]
      _ = 2 ^ (Finset.univ.filter (fun w => 2 ≤ fiber w)).card := by
            simp

end Omega.Zeta
