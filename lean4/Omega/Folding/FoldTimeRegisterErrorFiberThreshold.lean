import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.Folding.Fiber

namespace Omega

open scoped BigOperators

/-- For each visible state `x`, a decoder `g x` can recover at most one successful preimage per
tag. Summing that per-fiber pigeonhole bound gives the global success threshold. -/
theorem paper_fold_time_register_error_fiber_threshold (m : Nat) (T : Type) [Fintype T]
    [DecidableEq T] (α : Word m → T) (g : X m → T → Word m) :
    let succ := ((Finset.univ : Finset (Word m)).filter fun ω => g (Fold ω) (α ω) = ω).card
    succ ≤ ∑ x : X m, min (X.fiberMultiplicity x) (Fintype.card T) := by
  dsimp
  classical
  let successFiber : X m → Finset (Word m) := fun x =>
    (X.fiber x).filter fun ω => g x (α ω) = ω
  have hDisjoint :
      (↑(Finset.univ : Finset (X m)) : Set (X m)).PairwiseDisjoint successFiber := by
    intro x _ y _ hxy
    rw [Function.onFun, Finset.disjoint_left]
    intro ω hωx hωy
    rw [Finset.mem_filter] at hωx hωy
    exact hxy <| (X.mem_fiber.mp hωx.1).symm.trans (X.mem_fiber.mp hωy.1)
  have hUnion :
      ((Finset.univ : Finset (Word m)).filter fun ω => g (Fold ω) (α ω) = ω) =
        (Finset.univ : Finset (X m)).biUnion successFiber := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · intro hω
      refine ⟨Fold ω, ?_⟩
      rw [Finset.mem_filter]
      exact ⟨X.mem_fiber_Fold ω, by simpa using hω⟩
    · rintro ⟨x, hω⟩
      rw [Finset.mem_filter] at hω
      have hfold : Fold ω = x := X.mem_fiber.mp hω.1
      simpa [hfold] using hω.2
  have hpartition :
      ((Finset.univ : Finset (Word m)).filter fun ω => g (Fold ω) (α ω) = ω).card =
        ∑ x : X m, (successFiber x).card := by
    calc
      ((Finset.univ : Finset (Word m)).filter fun ω => g (Fold ω) (α ω) = ω).card
          = ((Finset.univ : Finset (X m)).biUnion successFiber).card := by
              rw [hUnion]
      _ = ∑ x : X m, (successFiber x).card := Finset.card_biUnion hDisjoint
  calc
    ((Finset.univ : Finset (Word m)).filter fun ω => g (Fold ω) (α ω) = ω).card
        = ∑ x : X m, (successFiber x).card := hpartition
    _ ≤ ∑ x : X m, min (X.fiberMultiplicity x) (Fintype.card T) := by
      refine Finset.sum_le_sum fun x _ => ?_
      have hFiber : (successFiber x).card ≤ X.fiberMultiplicity x := by
        simpa [successFiber, X.fiberMultiplicity] using
          Finset.card_le_card (Finset.filter_subset (fun ω => g x (α ω) = ω) (X.fiber x))
      have hTags : (successFiber x).card ≤ Fintype.card T := by
        calc
          (successFiber x).card = ((successFiber x).image α).card := by
            symm
            apply Finset.card_image_of_injOn
            intro ω₁ hω₁ ω₂ hω₂ hα
            simp [successFiber] at hω₁ hω₂
            calc
              ω₁ = g x (α ω₁) := hω₁.2.symm
              _ = g x (α ω₂) := by rw [hα]
              _ = ω₂ := hω₂.2
          _ ≤ Fintype.card T := Finset.card_le_univ _
      exact le_min hFiber hTags

end Omega
