import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.Conclusion.CapacityRamanujanPlateauLaw

namespace Omega.Folding

open Finset

private theorem card_eq_card_ge_sub_card_ge_succ {X : Type*} [Fintype X] [DecidableEq X]
    (d : X → Nat) (k : Nat) :
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
  have hcard : (Finset.univ.filter (fun x => d x = k)).card = A.card - B.card := by
    rw [← hsplit, Finset.card_sdiff_of_subset hBA]
  simpa [A, B] using hcard

private theorem card_ge_succ_le_card_ge {X : Type*} [Fintype X] [DecidableEq X] (d : X → Nat)
    (k : Nat) :
    Fintype.card {x : X // k + 1 ≤ d x} ≤ Fintype.card {x : X // k ≤ d x} := by
  rw [Fintype.card_of_subtype (Finset.univ.filter fun x => k + 1 ≤ d x) (by intro x; simp)]
  rw [Fintype.card_of_subtype (Finset.univ.filter fun x => k ≤ d x) (by intro x; simp)]
  exact Finset.card_le_card_of_injOn (fun x => x) (by
    intro x hx
    simp at hx ⊢
    omega) (by
    intro x _ y _ hxy
    exact hxy)

private theorem capacityCurve_mono {X : Type*} [Fintype X] (d : X → Nat) :
    Monotone (Omega.Conclusion.CapacityRamanujanPlateauLaw.capacityCurve d) := by
  intro s t hst
  unfold Omega.Conclusion.CapacityRamanujanPlateauLaw.capacityCurve
  exact Finset.sum_le_sum fun x _ => min_le_min_left _ hst

/-- `thm:fold-capacity-discrete-potential-histogram` -/
theorem paper_fold_capacity_discrete_potential_histogram {X : Type*} [Fintype X] [DecidableEq X]
    (d : X → Nat) :
    let N : Nat → Nat := fun t => Fintype.card {x : X // t ≤ d x}
    let C : Nat → Nat := fun t => Omega.Conclusion.CapacityRamanujanPlateauLaw.capacityCurve d t
    let h : Nat → Nat := fun k => Fintype.card {x : X // d x = k}
    (∀ k, 1 ≤ k → N k = C k - C (k - 1)) ∧
      (∀ k, h k = N k - N (k + 1)) ∧
      (∀ k, 1 ≤ k → h k = 2 * C k - C (k - 1) - C (k + 1)) := by
  classical
  dsimp
  have hN :
      ∀ k : Nat,
        1 ≤ k →
          Fintype.card {x : X // k ≤ d x} =
            Omega.Conclusion.CapacityRamanujanPlateauLaw.capacityCurve d k -
              Omega.Conclusion.CapacityRamanujanPlateauLaw.capacityCurve d (k - 1) := by
    intro k hk
    simpa [Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity] using
      (Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity_eq_card_ge d k hk).symm
  have hh :
      ∀ k : Nat,
        Fintype.card {x : X // d x = k} =
          Fintype.card {x : X // k ≤ d x} - Fintype.card {x : X // k + 1 ≤ d x} := by
    intro k
    rw [Fintype.card_of_subtype (Finset.univ.filter fun x => d x = k) (by intro x; simp)]
    rw [Fintype.card_of_subtype (Finset.univ.filter fun x => k ≤ d x) (by intro x; simp)]
    rw [Fintype.card_of_subtype (Finset.univ.filter fun x => k + 1 ≤ d x) (by intro x; simp)]
    exact card_eq_card_ge_sub_card_ge_succ d k
  refine ⟨hN, hh, ?_⟩
  intro k hk
  rw [hh k, hN k hk, hN (k + 1) (Nat.succ_le_succ (Nat.zero_le k))]
  have hle :
      Omega.Conclusion.CapacityRamanujanPlateauLaw.capacityCurve d (k + 1) -
          Omega.Conclusion.CapacityRamanujanPlateauLaw.capacityCurve d k ≤
        Omega.Conclusion.CapacityRamanujanPlateauLaw.capacityCurve d k -
          Omega.Conclusion.CapacityRamanujanPlateauLaw.capacityCurve d (k - 1) := by
    have htail := card_ge_succ_le_card_ge d k
    rwa [hN (k + 1) (Nat.succ_le_succ (Nat.zero_le k)), hN k hk] at htail
  let C : Nat → Nat := Omega.Conclusion.CapacityRamanujanPlateauLaw.capacityCurve d
  have hmono : C k ≤ C (k + 1) := capacityCurve_mono d (Nat.le_succ k)
  have hmono' : C (k - 1) ≤ C k := capacityCurve_mono d (by omega)
  have hdouble : C (k - 1) ≤ 2 * C k := by omega
  have hstep : C (k + 1) ≤ 2 * C k - C (k - 1) := by
    have hsum := Nat.add_le_add_left hle (C k)
    simpa [Nat.two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
      Nat.sub_add_cancel hmono, Nat.add_sub_assoc hmono'] using hsum
  apply Int.ofNat.inj
  calc
    (((C k - C (k - 1)) - (C (k + 1) - C k) : Nat) : Int)
        = ((C k - C (k - 1) : Nat) : Int) - ((C (k + 1) - C k : Nat) : Int) := by
            rw [Int.ofNat_sub hle]
    _ = ((C k : Int) - C (k - 1)) - ((C (k + 1) : Int) - C k) := by
          rw [Int.ofNat_sub hmono', Int.ofNat_sub hmono]
    _ = ((2 * C k - C (k - 1) - C (k + 1) : Nat) : Int) := by
          rw [Int.ofNat_sub hstep, Int.ofNat_sub hdouble]
          omega

end Omega.Folding
