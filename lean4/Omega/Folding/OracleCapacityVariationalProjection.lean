import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Omega.POM.BbitOracleCapacityClosedForm

namespace Omega

open scoped BigOperators

/-- Fiberwise variational characterization of the `B`-bit projection budget: every feasible
selection is bounded by the sum of the per-fiber caps, and that cap is attained by choosing
exactly `min(d_f(x), 2^B)` representatives in each fiber.
    prop:fold-oracle-variational-projection-characterization -/
theorem paper_fold_oracle_variational_projection_characterization
    {A X : Type*} [Fintype A] [Fintype X] [DecidableEq A] [DecidableEq X] (f : A → X) (B : Nat) :
    let T := 2 ^ B
    let feasible := fun S : Finset A => ∀ x : X, (S.filter fun a => f a = x).card ≤ T
    (∀ S : Finset A, feasible S -> S.card ≤ Omega.POM.taryOracleCapacity f T) ∧
      ∃ S : Finset A, feasible S ∧ S.card = Omega.POM.taryOracleCapacity f T := by
  classical
  dsimp
  let T : Nat := 2 ^ B
  let fiber : X → Finset A := fun x => Finset.univ.filter fun a => f a = x
  let feasible : Finset A → Prop := fun S => ∀ x : X, (S.filter fun a => f a = x).card ≤ T
  refine ⟨?_, ?_⟩
  · intro S hfeasible
    let slice : X → Finset A := fun x => S.filter fun a => f a = x
    have hUnion : S = (Finset.univ : Finset X).biUnion slice := by
      ext a
      simp [slice]
    have hDisjoint : ((Finset.univ : Finset X) : Set X).PairwiseDisjoint slice := by
      intro x _ y _ hxy
      refine Finset.disjoint_left.mpr ?_
      intro a hax hay
      have hx : f a = x := (by simpa [slice] using hax : a ∈ S ∧ f a = x).2
      have hy : f a = y := (by simpa [slice] using hay : a ∈ S ∧ f a = y).2
      exact hxy (hx.symm.trans hy)
    have hFiberCard : ∀ x : X, (fiber x).card = Fintype.card {a : A // f a = x} := by
      intro x
      exact (Fintype.card_of_subtype (p := fun a : A => f a = x) (fiber x) (by
        intro a
        simp [fiber])).symm
    have hCardBiUnion : ((Finset.univ : Finset X).biUnion slice).card = ∑ x : X, (slice x).card := by
      simpa [slice] using
        (Finset.card_biUnion hDisjoint :
          ((Finset.univ : Finset X).biUnion slice).card =
            ∑ x ∈ (Finset.univ : Finset X), (slice x).card)
    calc
      S.card = ((Finset.univ : Finset X).biUnion slice).card := by rw [hUnion]
      _ = ∑ x : X, (slice x).card := hCardBiUnion
      _ ≤ ∑ x : X, Nat.min ((fiber x).card) T := by
        refine Finset.sum_le_sum ?_
        intro x hx
        refine le_min ?_ (hfeasible x)
        exact Finset.card_le_card <| by
          intro a ha
          simp [slice, fiber] at ha ⊢
          exact ha.2
      _ = ∑ x : X, Nat.min (Fintype.card {a : A // f a = x}) T := by
        simp [hFiberCard]
      _ = Omega.POM.taryOracleCapacity f T := by
        simp [Omega.POM.taryOracleCapacity]
  · have hpick :
        ∀ x : X, ∃ U : Finset A, U ⊆ fiber x ∧ U.card = Nat.min ((fiber x).card) T := by
        intro x
        simpa using
          (Finset.exists_subset_card_eq (s := fiber x) (n := Nat.min ((fiber x).card) T)
            (Nat.min_le_left _ _))
    choose pick hpick_subset hpick_card using hpick
    let S : Finset A := (Finset.univ : Finset X).biUnion pick
    have hDisjoint : ((Finset.univ : Finset X) : Set X).PairwiseDisjoint pick := by
      intro x _ y _ hxy
      refine Finset.disjoint_left.mpr ?_
      intro a hax hay
      have hx : f a = x := by
        have : a ∈ fiber x := hpick_subset x hax
        simpa [fiber] using this
      have hy : f a = y := by
        have : a ∈ fiber y := hpick_subset y hay
        simpa [fiber] using this
      exact hxy (hx.symm.trans hy)
    refine ⟨S, ?_, ?_⟩
    · intro x
      have hsubset : (S.filter fun a => f a = x) ⊆ pick x := by
        intro a ha
        have haS : a ∈ S := (Finset.mem_filter.mp ha).1
        have hax : f a = x := (Finset.mem_filter.mp ha).2
        rcases (by simpa [S] using haS : ∃ y : X, a ∈ pick y) with ⟨y, hay⟩
        have hayFiber : f a = y := by
          have : a ∈ fiber y := hpick_subset y hay
          simpa [fiber] using this
        have hyx : y = x := hayFiber.symm.trans hax
        subst hyx
        simpa using hay
      exact (Finset.card_le_card hsubset).trans <| by
        rw [hpick_card x]
        exact Nat.min_le_right _ _
    · calc
        S.card = ∑ x : X, (pick x).card := by
          simpa [S] using Finset.card_biUnion hDisjoint
        _ = ∑ x : X, Nat.min ((fiber x).card) T := by
          simp [hpick_card]
        _ = ∑ x : X, Nat.min (Fintype.card {a : A // f a = x}) T := by
          have hFiberCard : ∀ x : X, (fiber x).card = Fintype.card {a : A // f a = x} := by
            intro x
            exact (Fintype.card_of_subtype (p := fun a : A => f a = x) (fiber x) (by
              intro a
              simp [fiber])).symm
          simp [hFiberCard]
        _ = Omega.POM.taryOracleCapacity f T := by
          simp [Omega.POM.taryOracleCapacity]

end Omega

/-- Root-level alias exposing the exact paper theorem name requested by the round script. -/
theorem paper_fold_oracle_variational_projection_characterization
    {A X : Type*} [Fintype A] [Fintype X] [DecidableEq A] [DecidableEq X] (f : A → X) (B : Nat) :
    let T := 2 ^ B
    let feasible := fun S : Finset A => ∀ x : X, (S.filter fun a => f a = x).card ≤ T
    (∀ S : Finset A, feasible S -> S.card ≤ Omega.POM.taryOracleCapacity f T) ∧
      ∃ S : Finset A, feasible S ∧ S.card = Omega.POM.taryOracleCapacity f T :=
  Omega.paper_fold_oracle_variational_projection_characterization f B
