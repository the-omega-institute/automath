import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Zeta.XiPickPoissonPrincipalMinorsPartition

open scoped BigOperators

namespace Omega.Zeta

theorem paper_xi_pick_poisson_partition_function_determinant {kappa : Nat}
    (P : XiPickPoissonGram kappa) (z : ℝ) :
    Finset.sum (Finset.powerset (Finset.univ : Finset (Fin kappa)))
        (fun I => z ^ I.card * xiPickPoissonPartitionWeight P I) =
      Finset.sum (Finset.range (kappa + 1))
        (fun r =>
          z ^ r *
            Finset.sum
              ((Finset.powerset (Finset.univ : Finset (Fin kappa))).filter (fun I => I.card = r))
              (xiPickPoissonPartitionWeight P)) := by
  classical
  rw [Finset.sum_powerset, Finset.card_univ, Fintype.card_fin]
  refine Finset.sum_congr rfl ?_
  intro r hr
  calc
    Finset.sum (Finset.powersetCard r (Finset.univ : Finset (Fin kappa)))
        (fun I => z ^ I.card * xiPickPoissonPartitionWeight P I) =
      Finset.sum (Finset.powersetCard r (Finset.univ : Finset (Fin kappa)))
        (fun I => z ^ r * xiPickPoissonPartitionWeight P I) := by
          apply Finset.sum_congr rfl
          intro I hI
          simp [(Finset.mem_powersetCard.mp hI).2]
    _ =
      z ^ r *
        Finset.sum (Finset.powersetCard r (Finset.univ : Finset (Fin kappa)))
          (xiPickPoissonPartitionWeight P) := by
            symm
            exact Finset.mul_sum _ _ _
    _ =
      z ^ r *
        Finset.sum
          ((Finset.powerset (Finset.univ : Finset (Fin kappa))).filter (fun I => I.card = r))
          (xiPickPoissonPartitionWeight P) := by
            rw [Finset.powersetCard_eq_filter]
