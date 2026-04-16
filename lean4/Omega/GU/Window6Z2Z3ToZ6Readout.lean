import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic

namespace Omega.GU

open Finset

/-- The parity-sum character on `(ℤ/2)^3`. -/
def window6ParityCharacter (x : Fin 3 → ZMod 2) : ZMod 2 :=
  x 0 + x 1 + x 2

/-- A linear `ℤ/2`-valued character specified by its coefficient vector. -/
def linearCharacter (a : Fin 3 → ZMod 2) (x : Fin 3 → ZMod 2) : ZMod 2 :=
  ∑ i, a i * x i

/-- Precomposition by a permutation of the three coordinates. -/
def precomposePerm (σ : Equiv.Perm (Fin 3)) (x : Fin 3 → ZMod 2) : Fin 3 → ZMod 2 :=
  fun i => x (σ i)

/-- `S₃`-invariance of a character on `(ℤ/2)^3`. -/
def s3Invariant (χ : (Fin 3 → ZMod 2) → ZMod 2) : Prop :=
  ∀ σ : Equiv.Perm (Fin 3), ∀ x, χ (precomposePerm σ x) = χ x

/-- The standard basis vector in coordinate `i`. -/
def basisVec (i : Fin 3) : Fin 3 → ZMod 2 :=
  fun j => if j = i then 1 else 0

/-- The canonical CRT equivalence `(ℤ/2) × (ℤ/3) ≃ ℤ/6`. -/
noncomputable def z2z3ToZ6 : ZMod 2 × ZMod 3 ≃+* ZMod 6 :=
  (ZMod.chineseRemainder (by decide : Nat.Coprime 2 3)).symm

/-- A readout factors through `ℤ/6`. -/
def factorsThroughZ6 (ψ : ZMod 2 × ZMod 3 → ZMod 6) : Prop :=
  ∃ θ : ZMod 6 → ZMod 6, ψ = θ ∘ z2z3ToZ6

theorem linearCharacter_basisVec (a : Fin 3 → ZMod 2) (i : Fin 3) :
    linearCharacter a (basisVec i) = a i := by
  fin_cases i <;> simp [linearCharacter, basisVec]

theorem precomposePerm_basisVec (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    precomposePerm σ (basisVec i) = basisVec (σ⁻¹ i) := by
  ext j
  by_cases h : j = σ.symm i
  · have hs : σ j = i := by
      simp [h]
    simp [precomposePerm, basisVec, h]
  · have hs : σ j ≠ i := by
      intro hs
      apply h
      simpa using congrArg σ.symm hs
    simp [precomposePerm, basisVec, h, hs]

theorem zero_coeffs_give_trivial_character (a : Fin 3 → ZMod 2)
    (ha : a = 0) :
    ∀ x, linearCharacter a x = 0 := by
  intro x
  simp [linearCharacter, ha]

theorem every_readout_factorsThroughZ6 (ψ : ZMod 2 × ZMod 3 → ZMod 6) :
    factorsThroughZ6 ψ := by
  refine ⟨ψ ∘ z2z3ToZ6.symm, ?_⟩
  ext x
  simp [z2z3ToZ6]

/-- Paper-facing wrapper: the unique nontrivial `S₃`-invariant `ℤ/2`-character is the parity sum,
    and the resulting `ℤ/2 × ℤ/3` readout factors through `ℤ/6`.
    thm:window6-z2z3-to-z6-readout -/
theorem paper_window6_z2z3_to_z6_readout
    (a : Fin 3 → ZMod 2)
    (hinv : s3Invariant (linearCharacter a))
    (hnontrivial : ∃ x, linearCharacter a x ≠ 0) :
    linearCharacter a = window6ParityCharacter ∧
      Nonempty (ZMod 2 × ZMod 3 ≃+* ZMod 6) ∧
      (∀ ψ : ZMod 2 × ZMod 3 → ZMod 6, factorsThroughZ6 ψ) := by
  have h01raw := hinv (Equiv.swap 0 1) (basisVec 0)
  have h12raw := hinv (Equiv.swap 1 2) (basisVec 1)
  have h01 : a 1 = a 0 := by
    simpa [precomposePerm_basisVec, linearCharacter_basisVec] using h01raw
  have h12 : a 2 = a 1 := by
    simpa [precomposePerm_basisVec, linearCharacter_basisVec] using h12raw
  have hzero_impossible : a 0 ≠ 0 := by
    intro h0
    have ha : a = 0 := by
      ext i
      fin_cases i
      · exact h0
      · simpa [h0] using h01
      · simpa [h0] using h12.trans h01
    rcases hnontrivial with ⟨x, hx⟩
    exact hx ((zero_coeffs_give_trivial_character a ha) x)
  set x : ZMod 2 := a 0
  have hxneq : x ≠ 0 := by
    simpa [x] using hzero_impossible
  have hxone : x = 1 := by
    have hclassified : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by
      decide
    have hvals : x = 0 ∨ x = 1 := hclassified x
    exact hvals.resolve_left hxneq
  have hone : a 0 = 1 := by
    simpa [x] using hxone
  have h1one : a 1 = 1 := by
    exact h01.trans hxone
  have h2one : a 2 = 1 := by
    exact h12.trans h1one
  have ha_one : a = fun _ => (1 : ZMod 2) := by
    ext i
    fin_cases i
    · exact hone
    · exact h1one
    · exact h2one
  refine ⟨?_, ⟨z2z3ToZ6⟩, every_readout_factorsThroughZ6⟩
  ext x
  simp [window6ParityCharacter, linearCharacter, ha_one, Fin.sum_univ_three]

end Omega.GU
