import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.Conclusion.BudgetCurveExactTailDifferenceReconstruction
import Omega.Conclusion.CapacityRamanujanPlateauLaw

namespace Omega.Conclusion

open Finset
open scoped BigOperators

/-- Paper-facing package for the finite-support equivalence between the multiplicity histogram,
tail counts, capacity jumps, and moment sums attached to a finite multiplicity function. -/
def FiniteMultiplicityDataEquivalent {X : Type*} [Fintype X]
    (h N C S : ℕ → ℕ) : Prop :=
  ∃ M : ℕ,
    (∀ k, M < k → h k = 0) ∧
    (∀ t, 1 ≤ t → N t = C t - C (t - 1)) ∧
    (∀ k, h k = N k - N (k + 1)) ∧
    (∀ q, S q = Finset.sum (Finset.range (M + 1)) (fun k => h k * k ^ q))

section

variable {X : Type*} [Fintype X] [DecidableEq X]

private theorem count_eq_tail_sub_tail_succ (d : X → ℕ) (k : ℕ) :
    (Finset.univ.filter (fun x => d x = k)).card =
      (Finset.univ.filter fun x => k ≤ d x).card -
        (Finset.univ.filter fun x => k + 1 ≤ d x).card := by
  let A : Finset X := Finset.univ.filter fun x => k ≤ d x
  let B : Finset X := Finset.univ.filter fun x => k + 1 ≤ d x
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

omit [DecidableEq X] in
private theorem value_le_totalMultiplicity (d : X → ℕ) (x : X) :
    d x ≤ ∑ y, d y := by
  classical
  simpa using
    (Finset.single_le_sum (f := fun y : X => d y) (fun y _ => Nat.zero_le (d y))
      (Finset.mem_univ x))

private theorem histogram_vanishes_above_totalMultiplicity (d : X → ℕ) (k : ℕ)
    (hk : (∑ x, d x) < k) :
    Fintype.card {x // d x = k} = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hpos
  rw [Fintype.card_pos_iff] at hpos
  rcases hpos with ⟨⟨x, hx⟩⟩
  have hle := value_le_totalMultiplicity d x
  omega

private theorem moment_sum_eq_histogram_sum (d : X → ℕ) (q : ℕ) :
    (Finset.sum (Finset.univ : Finset X) fun x => d x ^ q) =
      Finset.sum (Finset.range ((Finset.sum (Finset.univ : Finset X) d) + 1))
        (fun k => Fintype.card {x // d x = k} * k ^ q) := by
  classical
  let M : ℕ := ∑ x, d x
  calc
    Finset.sum (Finset.univ : Finset X) (fun x => d x ^ q)
        =
        Finset.sum (Finset.univ : Finset X)
          (fun x => Finset.sum (Finset.range (M + 1)) (fun k => if d x = k then k ^ q else 0)) := by
          apply Finset.sum_congr rfl
          intro x hx
          have hxM : d x < M + 1 := Nat.lt_succ_of_le (value_le_totalMultiplicity d x)
          rw [Finset.sum_eq_single_of_mem (d x) (Finset.mem_range.mpr hxM)]
          · simp
          · intro k hk hneq
            by_cases hdk : d x = k
            · exfalso
              exact hneq hdk.symm
            · simp [hdk]
    _ =
        Finset.sum (Finset.range (M + 1))
          (fun k => Finset.sum (Finset.univ : Finset X) (fun x => if d x = k then k ^ q else 0)) := by
          rw [Finset.sum_comm]
    _ =
        Finset.sum (Finset.range (M + 1))
          (fun k => Finset.sum ((Finset.univ : Finset X).filter (fun x => d x = k)) fun _ => k ^ q) := by
            apply Finset.sum_congr rfl
            intro k hk
            calc
              Finset.sum (Finset.univ : Finset X) (fun x => if d x = k then k ^ q else 0)
                  = Finset.sum ((Finset.univ : Finset X).filter (fun x => d x = k)) (fun _ => k ^ q) := by
                      rw [Finset.sum_filter]
              _ = Finset.sum ((Finset.univ : Finset X).filter (fun x => d x = k)) fun _ => k ^ q := by
                    rfl
    _ = Finset.sum (Finset.range (M + 1)) (fun k => Fintype.card {x // d x = k} * k ^ q) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Fintype.card_of_subtype (Finset.univ.filter fun x => d x = k) (by
            intro x
            simp)]
          rw [Finset.card_eq_sum_ones, Finset.sum_mul]
          simp

/-- `thm:conclusion-capacity-finite-completeness` -/
theorem paper_conclusion_capacity_finite_completeness_internal (d : X → ℕ) :
    let h : ℕ → ℕ := fun k => Fintype.card {x : X // d x = k};
    let N : ℕ → ℕ := fun t => Fintype.card {x : X // t ≤ d x};
    let C : ℕ → ℕ := fun t => Omega.Conclusion.CapacityRamanujanPlateauLaw.capacityCurve d t;
    FiniteMultiplicityDataEquivalent (X := X) h N C
      (fun q => Finset.sum (Finset.univ : Finset X) (fun x => d x ^ q)) := by
  classical
  dsimp [FiniteMultiplicityDataEquivalent]
  refine ⟨∑ x, d x, ?_, ?_, ?_, ?_⟩
  · intro k hk
    exact histogram_vanishes_above_totalMultiplicity d k hk
  · intro t ht
    simpa [CapacityRamanujanPlateauLaw.deltaCapacity] using
      (CapacityRamanujanPlateauLaw.deltaCapacity_eq_card_ge d t ht).symm
  · intro k
    rw [Fintype.card_of_subtype (Finset.univ.filter fun x => d x = k) (by
      intro x
      simp)]
    rw [Fintype.card_of_subtype (Finset.univ.filter fun x => k ≤ d x) (by
      intro x
      simp)]
    rw [Fintype.card_of_subtype (Finset.univ.filter fun x => k + 1 ≤ d x) (by
      intro x
      simp)]
    exact count_eq_tail_sub_tail_succ (d := d) (k := k)
  · intro q
    simpa using (moment_sum_eq_histogram_sum (d := d) (q := q))

end

/-- `thm:conclusion-capacity-finite-completeness` -/
theorem paper_conclusion_capacity_finite_completeness {X : Type*} [Fintype X] (d : X → ℕ) :
    let h : ℕ → ℕ := fun k => Fintype.card {x : X // d x = k};
    let N : ℕ → ℕ := fun t => Fintype.card {x : X // t ≤ d x};
    let C : ℕ → ℕ := fun t => Omega.Conclusion.CapacityRamanujanPlateauLaw.capacityCurve d t;
    FiniteMultiplicityDataEquivalent (X := X) h N C
      (fun q => Finset.sum (Finset.univ : Finset X) (fun x => d x ^ q)) := by
  classical
  exact paper_conclusion_capacity_finite_completeness_internal (X := X) d

end Omega.Conclusion
