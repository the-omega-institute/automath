import Mathlib.Tactic
import Omega.Conclusion.CapacityRamanujanPlateauLaw

namespace Omega.Conclusion.BudgetCurveExactTailDifferenceReconstruction

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

private theorem card_eq_card_ge_sub_card_ge_succ (d : α → ℕ) (k : ℕ) :
    (Finset.univ.filter (fun x => d x = k)).card =
      (Finset.univ.filter fun x => k ≤ d x).card -
        (Finset.univ.filter fun x => k + 1 ≤ d x).card := by
  classical
  let A : Finset α := Finset.univ.filter fun x => k ≤ d x
  let B : Finset α := Finset.univ.filter fun x => k + 1 ≤ d x
  have hBA : B ⊆ A := by
    intro x hx
    simp [A, B] at hx ⊢
    omega
  have hsplit : A \ B = Finset.univ.filter (fun x => d x = k) := by
    ext x
    simp [A, B]
    omega
  have hcard :
      (Finset.univ.filter (fun x => d x = k)).card = A.card - B.card := by
    rw [← hsplit, Finset.card_sdiff_of_subset hBA]
  simpa [A, B] using hcard

omit [DecidableEq α] in
private theorem deltaCapacity_eq_count_ge (d : α → ℕ) (s : ℕ) (hs : 1 ≤ s) :
    Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity d s = #{x | s ≤ d x} := by
  rw [Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity_eq_card_ge d s hs]
  exact Fintype.card_of_subtype (Finset.univ.filter fun x => s ≤ d x) (by
    intro x
    simp)

/-- Paper seed: the discrete budget curve jump is the tail count, and tail differences recover
    the exact multiplicity histogram.
    thm:conclusion-budget-curve-exact-tail-difference-reconstruction -/
theorem paper_conclusion_budget_curve_exact_tail_difference_reconstruction_seeds
    (d : α → ℕ) (s k : ℕ) (hs : 1 ≤ s) (hk : 1 ≤ k) :
    Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity d s =
      #{x | s ≤ d x} ∧
      #{x | d x = k} =
        Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity d k -
          Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity d (k + 1) ∧
      (∀ d' : α → ℕ,
        (∀ t : ℕ,
          Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity d t =
            Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity d' t) →
        #{x | d x = k} = #{x | d' x = k}) := by
  refine ⟨deltaCapacity_eq_count_ge d s hs, ?_, ?_⟩
  · rw [deltaCapacity_eq_count_ge d k hk,
      deltaCapacity_eq_count_ge d (k + 1) (Nat.succ_le_succ (Nat.zero_le k))]
    simpa [Nat.succ_le_iff] using card_eq_card_ge_sub_card_ge_succ (α := α) d k
  · intro d' hdelta
    calc
      #{x | d x = k}
          = Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity d k -
              Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity d (k + 1) := by
              rw [deltaCapacity_eq_count_ge d k hk,
                deltaCapacity_eq_count_ge d (k + 1) (Nat.succ_le_succ (Nat.zero_le k))]
              simpa [Nat.succ_le_iff] using card_eq_card_ge_sub_card_ge_succ (α := α) d k
      _ = Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity d' k -
            Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity d' (k + 1) := by
            rw [hdelta k, hdelta (k + 1)]
      _ = #{x | d' x = k} := by
            rw [deltaCapacity_eq_count_ge d' k hk,
              deltaCapacity_eq_count_ge d' (k + 1) (Nat.succ_le_succ (Nat.zero_le k))]
            simpa [Nat.succ_le_iff] using (card_eq_card_ge_sub_card_ge_succ (α := α) d' k).symm

end Omega.Conclusion.BudgetCurveExactTailDifferenceReconstruction
