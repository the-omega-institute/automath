import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete symmetric-monoidal jump data on the rank-two orientation torsor. The jump observable
is a monoid homomorphism from the permutation group of two letters to the additive group
`ZMod 2`. -/
structure conclusion_monoidal_jump_theory_a2torsion_classification_data where
  jump : Equiv.Perm (Fin 2) → ZMod 2
  jump_mul : ∀ σ τ, jump (σ * τ) = jump σ + jump τ

namespace conclusion_monoidal_jump_theory_a2torsion_classification_data

/-- The nontrivial transposition of the two orientation sheets. -/
def transposition : Equiv.Perm (Fin 2) :=
  Equiv.swap 0 1

/-- The invariant extracted from the transposition generator. -/
def transpositionInvariant
    (D : conclusion_monoidal_jump_theory_a2torsion_classification_data) : ZMod 2 :=
  D.jump transposition

/-- A concrete monoidal jump observable on the two-sheet orientation torsor. -/
def isMonoidalJump (f : Equiv.Perm (Fin 2) → ZMod 2) : Prop :=
  ∀ σ τ, f (σ * τ) = f σ + f τ

/-- The orientation-torsor extension realizing a prescribed `ZMod 2` value on the odd sheet. -/
def orientationExtension (a : ZMod 2) (σ : Equiv.Perm (Fin 2)) : ZMod 2 :=
  if σ = 1 then 0 else a

/-- The transposition invariant is two-torsion. -/
def classifiedByTwoTorsion
    (D : conclusion_monoidal_jump_theory_a2torsion_classification_data) : Prop :=
  D.transpositionInvariant + D.transpositionInvariant = 0

/-- The jump datum is trivial exactly when the extracted transposition invariant vanishes. -/
def trivialIffZero
    (D : conclusion_monoidal_jump_theory_a2torsion_classification_data) : Prop :=
  (∀ σ, D.jump σ = 0) ↔ D.transpositionInvariant = 0

/-- Every possible two-torsion orientation invariant is realized by an orientation-torsor
extension. -/
def extensionRealizesAll
    (_D : conclusion_monoidal_jump_theory_a2torsion_classification_data) : Prop :=
  ∀ a : ZMod 2, ∃ f : Equiv.Perm (Fin 2) → ZMod 2,
    isMonoidalJump f ∧ f transposition = a

end conclusion_monoidal_jump_theory_a2torsion_classification_data

open conclusion_monoidal_jump_theory_a2torsion_classification_data

/-- Paper label: `thm:conclusion-monoidal-jump-theory-a2torsion-classification`. -/
theorem paper_conclusion_monoidal_jump_theory_a2torsion_classification
    (D : conclusion_monoidal_jump_theory_a2torsion_classification_data) :
    D.classifiedByTwoTorsion ∧ D.trivialIffZero ∧ D.extensionRealizesAll := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [classifiedByTwoTorsion, transpositionInvariant] using
      (ZModModule.add_self (D.jump transposition))
  · constructor
    · intro h
      exact h transposition
    · intro h σ
      have hsquare : transposition * transposition = 1 := by
        ext i
        fin_cases i <;> simp [transposition]
      have hid : D.jump 1 = 0 := by
        calc
          D.jump 1 = D.jump (transposition * transposition) := by rw [hsquare]
          _ = D.jump transposition + D.jump transposition := D.jump_mul transposition transposition
          _ = 0 := by
            have h' : D.jump transposition = 0 := by
              simpa [transpositionInvariant] using h
            rw [h']
            simp
      have hσ : σ = 1 ∨ σ = transposition := by
        fin_cases σ <;> simp [transposition]
      rcases hσ with rfl | rfl
      · exact hid
      · exact h
  · intro a
    refine ⟨orientationExtension a, ?_, ?_⟩
    · intro σ τ
      fin_cases σ <;> fin_cases τ <;>
        simp [orientationExtension, ZModModule.add_self]
    · have hne : transposition ≠ (1 : Equiv.Perm (Fin 2)) := by
        intro h
        have happ := congrArg (fun σ : Equiv.Perm (Fin 2) => σ 0) h
        norm_num [transposition] at happ
      simp [orientationExtension, hne]

end Omega.Conclusion
