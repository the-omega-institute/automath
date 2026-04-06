import Omega.Core.WalshStokesSingleton
import Mathlib.Tactic

namespace Omega.Core

open scoped BigOperators

abbrev BoundaryWords (A : Finset (Fin n)) := {w : Word n // ∀ i ∈ A, w i = false}
abbrev DeltaSubsets (A : Finset (Fin n)) := {B : Finset (Fin n) // B ⊆ A}

/-- Signed hypercube sum. -/
def signedHypercubeSum (n : Nat) (f : Word n → ℤ) : ℤ :=
  ∑ w : Word n, (-1 : ℤ) ^ ((Finset.univ.filter (fun i => w i = true)).card) * f w

/-- Flip every bit in a finite coordinate set. -/
def flipSet (A : Finset (Fin n)) (w : Word n) : Word n :=
  fun i => if i ∈ A then !(w i) else w i

/-- Clear every bit in a finite coordinate set. -/
def clearBits (A : Finset (Fin n)) (w : Word n) : Word n :=
  fun i => if i ∈ A then false else w i

/-- The active coordinates of `w` inside `A`. -/
def activeBits (A : Finset (Fin n)) (w : Word n) : Finset (Fin n) :=
  A.filter fun i => w i = true

/-- Higher-order discrete derivative along a finite coordinate set.
    thm:discussion-walsh-stokes-higher-flux -/
def deltaSet (A : Finset (Fin n)) (f : Word n → ℤ) (w : Word n) : ℤ :=
  ∑ B : DeltaSubsets A, (-1 : ℤ) ^ B.1.card * f (flipSet B.1 w)

/-- `A`-flux as the boundary sum over the `A`-face.
    thm:discussion-walsh-stokes-higher-flux -/
def walshFlux (A : Finset (Fin n)) (f : Word n → ℤ) : ℤ :=
  ∑ w : BoundaryWords A, deltaSet A f w.1

@[simp] theorem flipSet_apply (A : Finset (Fin n)) (w : Word n) (i : Fin n) :
    flipSet A w i = if i ∈ A then !(w i) else w i :=
  rfl

@[simp] theorem clearBits_apply (A : Finset (Fin n)) (w : Word n) (i : Fin n) :
    clearBits A w i = if i ∈ A then false else w i :=
  rfl

@[simp] theorem activeBits_mem (A : Finset (Fin n)) (w : Word n) (i : Fin n) :
    i ∈ activeBits A w ↔ i ∈ A ∧ w i = true := by
  simp [activeBits]

@[simp] theorem flipBit_comm (i j : Fin n) (w : Word n) :
    flipBit i (flipBit j w) = flipBit j (flipBit i w) := by
  by_cases hij : i = j
  · subst hij
    simp [flipBit_involutive]
  · funext k
    by_cases hki : k = i
    · subst hki
      simp [flipBit_apply_same, flipBit_apply_ne, hij]
    · by_cases hkj : k = j
      · subst hkj
        simp [flipBit_apply_same, flipBit_apply_ne, hki]
      · simp [flipBit_apply_ne, hki, hkj]

theorem clearBits_flipSet {A B : Finset (Fin n)} {w : Word n}
    (hB : B ⊆ A) (hw : ∀ i ∈ A, w i = false) :
    clearBits A (flipSet B w) = w := by
  funext i
  by_cases hiA : i ∈ A
  · have hwi : w i = false := hw i hiA
    simp [clearBits, hiA, hwi]
  · have hiB : i ∉ B := fun hiB => hiA (hB hiB)
    simp [clearBits, flipSet, hiA, hiB]

theorem activeBits_flipSet {A B : Finset (Fin n)} {w : Word n}
    (hB : B ⊆ A) (hw : ∀ i ∈ A, w i = false) :
    activeBits A (flipSet B w) = B := by
  ext i
  by_cases hiB : i ∈ B
  · have hiA : i ∈ A := hB hiB
    have hwi : w i = false := hw i hiA
    simp [activeBits, flipSet, hiA, hiB, hwi]
  · by_cases hiA : i ∈ A
    · have hwi : w i = false := hw i hiA
      simp [activeBits, flipSet, hiA, hiB, hwi]
    · simp [activeBits, hiA, hiB]

theorem flipSet_activeBits_clearBits (A : Finset (Fin n)) (w : Word n) :
    flipSet (activeBits A w) (clearBits A w) = w := by
  funext i
  by_cases hiA : i ∈ A
  · by_cases hwi : w i = true
    · simp [flipSet, clearBits, activeBits, hiA, hwi]
    · have hfalse : w i = false := by
        cases h : w i <;> simp_all
      simp [flipSet, clearBits, activeBits, hiA, hwi]
  · simp [flipSet, clearBits, activeBits, hiA]

/-- Single-coordinate derivatives commute.
    thm:discussion-walsh-stokes-higher-flux -/
theorem deltaBit_comm (i j : Fin n) (f : Word n → ℤ) :
    deltaBit i (deltaBit j f) = deltaBit j (deltaBit i f) := by
  funext w
  unfold deltaBit
  rw [flipBit_comm, flipBit_comm]
  ring

/-- Reindexing the boundary face after inserting one more constrained bit.
    thm:discussion-walsh-stokes-higher-flux -/
theorem walshFlux_insert {A : Finset (Fin n)} (i : Fin n) (hi : i ∉ A) (f : Word n → ℤ) :
    walshFlux (insert i A) f =
      ∑ w : {w : BoundaryWords A // w.1 i = false}, deltaSet (insert i A) f w.1.1 := by
  let e : BoundaryWords (insert i A) ≃ {w : BoundaryWords A // w.1 i = false} :=
    { toFun := fun w =>
        ⟨⟨w.1, fun j hj => w.2 j (Finset.mem_insert_of_mem hj)⟩, by
          simpa using w.2 i (by simp)⟩
      invFun := fun w =>
        ⟨w.1.1, by
          intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hjA
          · exact w.2
          · exact w.1.2 j hjA⟩
      left_inv := by
        intro w
        rfl
      right_inv := by
        intro w
        rfl }
  unfold walshFlux
  simpa using
    (Fintype.sum_equiv e
      (fun w : BoundaryWords (insert i A) => deltaSet (insert i A) f w.1)
      (fun w : {w : BoundaryWords A // w.1 i = false} => deltaSet (insert i A) f w.1.1)
      (by intro w; rfl))

/-- Constant signed sum vanishes for n ≥ 1.
    thm:discussion-walsh-stokes-higher-flux -/
theorem signedHypercubeSum_const (n : Nat) (hn : 1 ≤ n) (c : ℤ) :
    signedHypercubeSum n (fun _ => c) = 0 := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm]
  let e : Word (m + 1) ≃ Word m × Bool :=
    { toFun := fun w => (fun i => w i.succ, w 0)
      invFun := fun p => Fin.cons p.2 p.1
      left_inv := by
        intro w
        funext i
        refine Fin.cases ?_ ?_ i
        · rfl
        · intro j
          rfl
      right_inv := by
        intro p
        cases p
        rfl }
  have hs :
      signedHypercubeSum (m + 1) (fun _ => c) =
        ∑ p : Word m × Bool,
          (-1 : ℤ) ^ ((Finset.univ.filter (fun i => (e.symm p) i = true)).card) * c := by
    unfold signedHypercubeSum
    refine Fintype.sum_equiv e
      (fun w : Word (m + 1) => (-1 : ℤ) ^ ((Finset.univ.filter fun i => w i = true).card) * c)
      (fun p : Word m × Bool => (-1 : ℤ) ^ ((Finset.univ.filter fun i => (e.symm p) i = true).card) * c)
      ?_
    intro w
    have heq : e.symm (e w) = w := e.left_inv w
    exact congrArg (fun u : Word (m + 1) => (Finset.univ.filter fun i => u i = true).card) heq.symm |>
      fun h => congrArg (fun k : Nat => (-1 : ℤ) ^ k * c) h
  have hfalse (u : Word m) :
      (Finset.univ.filter (fun i : Fin (m + 1) => (e.symm (u, false)) i = true)).card =
        (Finset.univ.filter fun i : Fin m => u i = true).card := by
    simpa [e] using
      (Fin.card_filter_univ_succ (n := m) (p := fun i : Fin (m + 1) => (e.symm (u, false)) i = true))
  have htrue (u : Word m) :
      (Finset.univ.filter (fun i : Fin (m + 1) => (e.symm (u, true)) i = true)).card =
        (Finset.univ.filter fun i : Fin m => u i = true).card + 1 := by
    simpa [e] using
      (Fin.card_filter_univ_succ (n := m) (p := fun i : Fin (m + 1) => (e.symm (u, true)) i = true))
  rw [hs, Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro u hu
  rw [Fintype.sum_bool, hfalse, htrue, pow_succ]
  ring


/-- Higher-order Walsh--Stokes flux formula on a finite coordinate set.
    thm:discussion-walsh-stokes-higher-flux -/
theorem walshStokes_finset (A : Finset (Fin n)) (f : Word n → ℤ) :
    walshFlux A f =
      ∑ w : Word n, (-1 : ℤ) ^ ((A.filter fun i => w i = true).card) * f w := by
  let e : BoundaryWords A × DeltaSubsets A ≃ Word n :=
    { toFun := fun p => flipSet p.2.1 p.1.1
      invFun := fun w =>
        (⟨clearBits A w, by
            intro i hi
            simp [clearBits, hi]⟩,
          ⟨activeBits A w, by
            intro i hi
            exact (activeBits_mem A w i).mp hi |>.1⟩)
      left_inv := by
        intro p
        rcases p with ⟨w, B⟩
        rcases w with ⟨w, hw⟩
        rcases B with ⟨B, hB⟩
        apply Prod.ext
        · apply Subtype.ext
          exact clearBits_flipSet (A := A) (B := B) (w := w) hB hw
        · apply Subtype.ext
          exact activeBits_flipSet (A := A) (B := B) (w := w) hB hw
      right_inv := by
        intro w
        exact flipSet_activeBits_clearBits A w }
  unfold walshFlux deltaSet
  simpa [Fintype.sum_prod_type, activeBits] using
    (Fintype.sum_equiv e
      (fun p : BoundaryWords A × DeltaSubsets A =>
        (-1 : ℤ) ^ p.2.1.card * f (flipSet p.2.1 p.1.1))
      (fun w : Word n => (-1 : ℤ) ^ (activeBits A w).card * f w)
      (by
        intro p
        rcases p with ⟨w, B⟩
        rcases w with ⟨w, hw⟩
        rcases B with ⟨B, hB⟩
        have hactive : activeBits A (flipSet B w) = B :=
          activeBits_flipSet (A := A) (B := B) (w := w) hB hw
        simp [e, hactive]))

/-- The one-dimensional boundary variation dominates the Walsh bias.
    cor:discussion-walsh-bias-controlled-by-boundary-variation -/
theorem walshBias_le_boundaryVariation (A : Finset (Fin n)) (f : Word n → ℤ) :
    Int.natAbs (walshFlux A f) ≤
      ∑ w : BoundaryWords A, Int.natAbs (deltaSet A f w.1) := by
  unfold walshFlux
  simpa using nat_abs_sum_le (s := Finset.univ) (f := fun w : BoundaryWords A => deltaSet A f w.1)

/-- One-dimensional test case.
    thm:discussion-walsh-stokes-higher-flux -/
theorem signedHypercubeSum_one :
    signedHypercubeSum 1 (fun w => if w 0 = true then 1 else 0) = -1 := by
  native_decide

end Omega.Core
