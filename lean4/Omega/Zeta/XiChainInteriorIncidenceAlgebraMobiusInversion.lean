import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic
import Omega.Zeta.XiChainInteriorBooleanFlagClosedForm

namespace Omega.Zeta

open Finset
open scoped BigOperators

private theorem xi_chain_interior_incidence_algebra_mobius_inversion_local
    {m : Nat} (T : Finset (Fin m)) :
    ∀ (f g : Finset (Fin m) → Int),
      (∀ U, U ⊆ T → g U = ∑ S in U.powerset, f S) →
      f T = ∑ S in T.powerset, booleanIntervalSign S T * g S := by
  induction T using Finset.induction_on with
  | empty =>
      intro f g hfg
      have h0 := hfg ∅ (by simp)
      simpa [booleanIntervalSign] using h0.symm
  | @insert a T ha ih =>
      intro f g hfg
      let f' : Finset (Fin m) → Int := fun U => f (insert a U)
      let g' : Finset (Fin m) → Int := fun U => g (insert a U) - g U
      have hfg' : ∀ U, U ⊆ T → g' U = ∑ S in U.powerset, f' S := by
        intro U hUT
        have haU : a ∉ U := fun hau => ha (hUT hau)
        have hdisj : Disjoint U.powerset (U.powerset.image (insert a)) := by
          refine Finset.disjoint_left.2 ?_
          intro V hV hVim
          rcases Finset.mem_image.mp hVim with ⟨W, hW, rfl⟩
          have haV : a ∉ V := Finset.notMem_of_mem_powerset_of_notMem hV haU
          exact haV (by simp)
        have hinj : Function.Injective (insert a : Finset (Fin m) → Finset (Fin m)) := by
          intro S₁ S₂ hS
          ext x
          by_cases hx : x = a
          · simp [hx]
          · have := congrArg (fun Z => x ∈ Z) hS
            simpa [hx] using this
        calc
          g' U = g (insert a U) - g U := by rfl
          _ = (∑ S in (insert a U).powerset, f S) - ∑ S in U.powerset, f S := by
                rw [hfg (insert a U) (by
                  intro x hx
                  exact Finset.mem_insert_of_mem (hUT hx)), hfg U (by
                    intro x hx
                    exact Finset.mem_insert_of_mem (hUT hx))]
          _ = (∑ S in U.powerset, f S) + ∑ S in U.powerset.image (insert a), f S
                - ∑ S in U.powerset, f S := by
                rw [Finset.powerset_insert, Finset.sum_union hdisj]
          _ = ∑ S in U.powerset.image (insert a), f S := by abel
          _ = ∑ S in U.powerset, f' S := by
                rw [Finset.sum_image hinj]
                intro S hS
                rfl
      have hsign_without :
          ∀ S, S ⊆ T → booleanIntervalSign S (insert a T) = -booleanIntervalSign S T := by
        intro S hST
        have hSins : S ⊆ insert a T := by
          intro x hx
          exact Finset.mem_insert_of_mem (hST hx)
        have hcard :
            (insert a T).card - S.card = (T.card - S.card) + 1 := by
          rw [Finset.card_insert_of_notMem ha]
          omega
        rw [booleanIntervalSign, booleanIntervalSign, if_pos hSins, if_pos hST, hcard, pow_succ]
        simpa [mul_comm]
      have hsign_with :
          ∀ S, S ⊆ T → booleanIntervalSign (insert a S) (insert a T) = booleanIntervalSign S T := by
        intro S hST
        have haS : a ∉ S := fun has => ha (hST has)
        have hSins : insert a S ⊆ insert a T := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx'
          · simp
          · exact Finset.mem_insert_of_mem (hST hx')
        have hcard :
            (insert a T).card - (insert a S).card = T.card - S.card := by
          rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem haS]
          omega
        rw [booleanIntervalSign, booleanIntervalSign, if_pos hSins, if_pos hST, hcard]
      have hdisjT : Disjoint T.powerset (T.powerset.image (insert a)) := by
        refine Finset.disjoint_left.2 ?_
        intro S hS hSim
        rcases Finset.mem_image.mp hSim with ⟨U, hU, rfl⟩
        have haS : a ∉ S := Finset.notMem_of_mem_powerset_of_notMem hS ha
        exact haS (by simp)
      have hinjT : Function.Injective (insert a : Finset (Fin m) → Finset (Fin m)) := by
        intro S₁ S₂ hS
        ext x
        by_cases hx : x = a
        · simp [hx]
        · have := congrArg (fun Z => x ∈ Z) hS
          simpa [hx] using this
      have hsplit :
          ∑ S in (insert a T).powerset, booleanIntervalSign S (insert a T) * g S =
            ∑ S in T.powerset, booleanIntervalSign S T * g' S := by
        rw [Finset.powerset_insert, Finset.sum_union hdisjT, Finset.sum_image hinjT]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro S hS
        rw [g', hsign_without S (Finset.mem_powerset.mp hS), hsign_with S (Finset.mem_powerset.mp hS)]
        ring
      calc
        f (insert a T) = f' T := by rfl
        _ = ∑ S in T.powerset, booleanIntervalSign S T * g' S := ih f' g' hfg'
        _ = ∑ S in (insert a T).powerset, booleanIntervalSign S (insert a T) * g S := hsplit.symm

theorem paper_xi_chain_interior_incidence_algebra_mobius_inversion (n : Nat) :
    let m := n - 1
    ∀ (f g : Finset (Fin m) → Int),
      (∀ T, g T = ∑ S in T.powerset, f S) →
      ∀ T, f T = ∑ S in T.powerset, booleanIntervalSign S T * g S := by
  intro m f g hfg T
  exact xi_chain_interior_incidence_algebra_mobius_inversion_local T f g (fun U _ => hfg U)

end Omega.Zeta
