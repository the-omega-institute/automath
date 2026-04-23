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
      (∀ U, U ⊆ T → g U = Finset.sum U.powerset f) →
      f T = Finset.sum T.powerset (fun S => booleanIntervalSign S T * g S) := by
  induction T using Finset.induction_on with
  | empty =>
      intro f g hfg
      have h0 := hfg ∅ (by simp)
      simpa [booleanIntervalSign] using h0.symm
  | @insert a T ha ih =>
      intro f g hfg
      let f' : Finset (Fin m) → Int := fun U => f (insert a U)
      let g' : Finset (Fin m) → Int := fun U => g (insert a U) - g U
      have hfg' : ∀ U, U ⊆ T → g' U = Finset.sum U.powerset f' := by
        intro U hUT
        have haU : a ∉ U := fun hau => ha (hUT hau)
        have hdisj : Disjoint U.powerset (U.powerset.image (insert a)) := by
          refine Finset.disjoint_left.2 ?_
          intro V hV hVim
          rcases Finset.mem_image.mp hVim with ⟨W, hW, rfl⟩
          have haV : a ∉ insert a W := Finset.notMem_of_mem_powerset_of_notMem hV haU
          exact haV (by simp)
        have hinj : Set.InjOn (insert a : Finset (Fin m) → Finset (Fin m)) ↑U.powerset := by
          intro S₁ hS₁ S₂ hS₂ hS
          have haS₁ : a ∉ S₁ := Finset.notMem_of_mem_powerset_of_notMem hS₁ haU
          have haS₂ : a ∉ S₂ := Finset.notMem_of_mem_powerset_of_notMem hS₂ haU
          ext x
          by_cases hx : x = a
          · subst hx
            simp [haS₁, haS₂]
          · have := congrArg (fun Z => x ∈ Z) hS
            simpa [hx] using this
        calc
          g' U = g (insert a U) - g U := by rfl
          _ = Finset.sum (insert a U).powerset f - Finset.sum U.powerset f := by
                rw [hfg (insert a U) (by
                  intro x hx
                  rcases Finset.mem_insert.mp hx with rfl | hx'
                  · simp
                  · exact Finset.mem_insert_of_mem (hUT hx')), hfg U (by
                    intro x hx
                    exact Finset.mem_insert_of_mem (hUT hx))]
          _ = Finset.sum U.powerset f + Finset.sum (U.powerset.image (insert a)) f
                - Finset.sum U.powerset f := by
                rw [Finset.powerset_insert, Finset.sum_union hdisj]
          _ = Finset.sum (U.powerset.image (insert a)) f := by abel
          _ = Finset.sum U.powerset f' := by
                simpa [f'] using
                  (Finset.sum_image (s := U.powerset) (g := insert a) (f := f) hinj)
      have hsign_without :
          ∀ S, S ⊆ T → booleanIntervalSign S (insert a T) = -booleanIntervalSign S T := by
        intro S hST
        have hSins : S ⊆ insert a T := by
          intro x hx
          exact Finset.mem_insert_of_mem (hST hx)
        have hcard :
            (insert a T).card - S.card = (T.card - S.card) + 1 := by
          have hcard_le : S.card ≤ T.card := Finset.card_le_card hST
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
        have haS : a ∉ insert a U := Finset.notMem_of_mem_powerset_of_notMem hS ha
        exact haS (by simp)
      have hinjT : Set.InjOn (insert a : Finset (Fin m) → Finset (Fin m)) ↑T.powerset := by
        intro S₁ hS₁ S₂ hS₂ hS
        have haS₁ : a ∉ S₁ := Finset.notMem_of_mem_powerset_of_notMem hS₁ ha
        have haS₂ : a ∉ S₂ := Finset.notMem_of_mem_powerset_of_notMem hS₂ ha
        ext x
        by_cases hx : x = a
        · subst hx
          simp [haS₁, haS₂]
        · have := congrArg (fun Z => x ∈ Z) hS
          simpa [hx] using this
      have hsplit :
          Finset.sum (insert a T).powerset (fun S => booleanIntervalSign S (insert a T) * g S) =
            Finset.sum T.powerset (fun S => booleanIntervalSign S T * g' S) := by
        rw [Finset.powerset_insert, Finset.sum_union hdisjT, Finset.sum_image hinjT]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro S hS
        simp_rw [g', hsign_without S (Finset.mem_powerset.mp hS), hsign_with S (Finset.mem_powerset.mp hS)]
        ring
      calc
        f (insert a T) = f' T := by rfl
        _ = Finset.sum T.powerset (fun S => booleanIntervalSign S T * g' S) := ih f' g' hfg'
        _ = Finset.sum (insert a T).powerset (fun S => booleanIntervalSign S (insert a T) * g S) :=
              hsplit.symm

theorem paper_xi_chain_interior_incidence_algebra_mobius_inversion (n : Nat) :
    let m := n - 1;
    ∀ (f g : Finset (Fin m) → Int),
      (∀ T, g T = Finset.sum T.powerset f) →
      ∀ T, f T = Finset.sum T.powerset (fun S => booleanIntervalSign S T * g S) := by
  dsimp
  intro f g hfg T
  exact xi_chain_interior_incidence_algebra_mobius_inversion_local T f g (fun U _ => hfg U)

end Omega.Zeta
