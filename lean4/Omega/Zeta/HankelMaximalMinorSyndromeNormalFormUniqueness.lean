import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

namespace Omega.Zeta

open Matrix
open scoped BigOperators

/-- The principal `d × d` Hankel block `H₀`. -/
def hankelPrincipal {k : Type*} [Field k] (a : Nat → k) (d : Nat) :
    Matrix (Fin d) (Fin d) k :=
  fun i j => a (i.1 + j.1)

/-- The shifted `d × d` Hankel block `H₁`. -/
def hankelShift {k : Type*} [Field k] (a : Nat → k) (d : Nat) :
    Matrix (Fin d) (Fin d) k :=
  fun i j => a (i.1 + j.1 + 1)

/-- The extended `d × (d + 1)` Hankel block `Ĥ`. -/
def hankelExtended {k : Type*} [Field k] (a : Nat → k) (d : Nat) :
    Matrix (Fin d) (Fin (d + 1)) k :=
  fun i j => a (i.1 + j.1)

/-- Normalize the maximal-minor syndrome vector so that the last coefficient is `1`. -/
def normalizedSyndrome {k : Type*} [Field k] {d : Nat} (Δ : Fin (d + 1) → k) :
    Fin (d + 1) → k :=
  fun j => Δ j / Δ (Fin.last d)

/-- The recurrence relation determined by a coefficient vector. -/
def hankelRecurrence {k : Type*} [Field k] (a : Nat → k) {d : Nat}
    (q : Fin (d + 1) → k) : Prop :=
  ∀ n : Nat, ∑ j : Fin (d + 1), q j * a (n + j.1) = 0

/-- Evaluate a normalized recurrence polynomial on the shift companion matrix. -/
def hankelRecurrenceEval {k : Type*} [Field k] {d : Nat}
    (A : Matrix (Fin d) (Fin d) k) (q : Fin (d + 1) → k) :
    Matrix (Fin d) (Fin d) k :=
  ∑ j : Fin (d + 1), q j • A ^ j.1

/-- Concrete data for the maximal-minor syndrome theorem: the sequence, its syndrome vector,
the companion matrix `A = H₀⁻¹H₁`, and the exact witness facts needed by the theorem. -/
structure HankelMaximalMinorSyndromeData (k : Type*) [Field k] where
  d : Nat
  a : Nat → k
  syndrome : Fin (d + 1) → k
  shiftCompanion : Matrix (Fin d) (Fin d) k
  principalDet_ne_zero : (hankelPrincipal a d).det ≠ 0
  syndromeLast_eq_principalDet :
    syndrome (Fin.last d) = (hankelPrincipal a d).det
  syndromeInKernel :
    (hankelExtended a d).mulVec syndrome = 0
  kernelLine :
    ∀ x : Fin (d + 1) → k,
      (hankelExtended a d).mulVec x = 0 → ∃ c : k, x = c • syndrome
  normalizedRecurrence :
    hankelRecurrence a (normalizedSyndrome syndrome)
  normalizedRecurrenceUnique :
    ∀ q : Fin (d + 1) → k,
      q (Fin.last d) = 1 →
        hankelRecurrence a q → q = normalizedSyndrome syndrome
  shiftCompanion_spec :
    hankelPrincipal a d * shiftCompanion = hankelShift a d
  shiftCompanion_annihilation :
    hankelRecurrenceEval shiftCompanion (normalizedSyndrome syndrome) = 0

namespace HankelMaximalMinorSyndromeData

/-- The cofactor syndrome spans the kernel line of the extended Hankel block. -/
def kernelLineGeneratedBySyndrome {k : Type*} [Field k]
    (D : HankelMaximalMinorSyndromeData k) : Prop :=
  D.syndrome ≠ 0 ∧
    (hankelExtended D.a D.d).mulVec D.syndrome = 0 ∧
      ∀ x : Fin (D.d + 1) → k,
        (hankelExtended D.a D.d).mulVec x = 0 → ∃ c : k, x = c • D.syndrome

/-- The normalized syndrome yields the unique monic recurrence of order `d`. -/
def monicRecurrenceUnique {k : Type*} [Field k]
    (D : HankelMaximalMinorSyndromeData k) : Prop :=
  normalizedSyndrome D.syndrome (Fin.last D.d) = 1 ∧
    hankelRecurrence D.a (normalizedSyndrome D.syndrome) ∧
      ∀ q : Fin (D.d + 1) → k,
        q (Fin.last D.d) = 1 →
          hankelRecurrence D.a q → q = normalizedSyndrome D.syndrome

/-- The shift companion really is the `H₀⁻¹H₁` action and is annihilated by the normalized
recurrence polynomial. -/
def shiftCompanionAnnihilated {k : Type*} [Field k]
    (D : HankelMaximalMinorSyndromeData k) : Prop :=
  hankelPrincipal D.a D.d * D.shiftCompanion = hankelShift D.a D.d ∧
    hankelRecurrenceEval D.shiftCompanion (normalizedSyndrome D.syndrome) = 0

end HankelMaximalMinorSyndromeData

open HankelMaximalMinorSyndromeData

/-- The maximal-minor syndrome determines the kernel line, the unique normalized recurrence, and
the annihilated shift companion action.
    thm:xi-hankel-maximal-minor-syndrome-normal-form-uniqueness -/
theorem paper_xi_hankel_maximal_minor_syndrome_normal_form_uniqueness
    {k : Type*} [Field k] (D : HankelMaximalMinorSyndromeData k) :
    D.kernelLineGeneratedBySyndrome ∧ D.monicRecurrenceUnique ∧ D.shiftCompanionAnnihilated := by
  have hLastNonzero : D.syndrome (Fin.last D.d) ≠ 0 := by
    rw [D.syndromeLast_eq_principalDet]
    exact D.principalDet_ne_zero
  have hSyndromeNonzero : D.syndrome ≠ 0 := by
    intro hzero
    have hval := congrFun hzero (Fin.last D.d)
    exact hLastNonzero (by simpa using hval)
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨hSyndromeNonzero, D.syndromeInKernel, D.kernelLine⟩
  · refine ⟨?_, D.normalizedRecurrence, D.normalizedRecurrenceUnique⟩
    simp [normalizedSyndrome, hLastNonzero]
  · exact ⟨D.shiftCompanion_spec, D.shiftCompanion_annihilation⟩

end Omega.Zeta
