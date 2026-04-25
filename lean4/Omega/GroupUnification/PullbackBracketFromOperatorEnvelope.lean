import Mathlib

namespace Omega.GroupUnification

universe u v

/-- Concrete data for transporting the commutator bracket on an operator submodule back to a type
via a `ℤ`-linear equivalence. -/
structure PullbackBracketFromOperatorEnvelopeData where
  V : Type u
  pullback_bracket_from_operator_envelope_instV : AddCommGroup V
  W : Type v
  pullback_bracket_from_operator_envelope_instW : AddCommGroup W
  pullback_bracket_from_operator_envelope_operatorSubmodule : Submodule ℤ (Module.End ℤ V)
  pullback_bracket_from_operator_envelope_Phi :
    W ≃ₗ[ℤ] pullback_bracket_from_operator_envelope_operatorSubmodule
  pullback_bracket_from_operator_envelope_closed :
    ∀ A B : pullback_bracket_from_operator_envelope_operatorSubmodule,
      A.1 * B.1 - B.1 * A.1 ∈ pullback_bracket_from_operator_envelope_operatorSubmodule

attribute [instance]
  PullbackBracketFromOperatorEnvelopeData.pullback_bracket_from_operator_envelope_instV
attribute [instance]
  PullbackBracketFromOperatorEnvelopeData.pullback_bracket_from_operator_envelope_instW

namespace PullbackBracketFromOperatorEnvelopeData

/-- The commutator bracket inside the chosen operator submodule. -/
def pullback_bracket_from_operator_envelope_operatorBracket
    (D : PullbackBracketFromOperatorEnvelopeData)
    (A B : D.pullback_bracket_from_operator_envelope_operatorSubmodule) :
    D.pullback_bracket_from_operator_envelope_operatorSubmodule :=
  ⟨A.1 * B.1 - B.1 * A.1, D.pullback_bracket_from_operator_envelope_closed A B⟩

/-- The transported bracket on `W`. -/
def pullback_bracket_from_operator_envelope_bracket
    (D : PullbackBracketFromOperatorEnvelopeData) :
    D.W → D.W → D.W := fun x y =>
  D.pullback_bracket_from_operator_envelope_Phi.symm
    (D.pullback_bracket_from_operator_envelope_operatorBracket
      (D.pullback_bracket_from_operator_envelope_Phi x)
      (D.pullback_bracket_from_operator_envelope_Phi y))

lemma pullback_bracket_from_operator_envelope_operatorBracket_add_left
    (D : PullbackBracketFromOperatorEnvelopeData)
    (A₁ A₂ B : D.pullback_bracket_from_operator_envelope_operatorSubmodule) :
    D.pullback_bracket_from_operator_envelope_operatorBracket (A₁ + A₂) B =
      D.pullback_bracket_from_operator_envelope_operatorBracket A₁ B +
        D.pullback_bracket_from_operator_envelope_operatorBracket A₂ B := by
  apply Subtype.ext
  simp [pullback_bracket_from_operator_envelope_operatorBracket, sub_eq_add_neg, add_mul, mul_add]
  abel_nf

lemma pullback_bracket_from_operator_envelope_operatorBracket_add_right
    (D : PullbackBracketFromOperatorEnvelopeData)
    (A B₁ B₂ : D.pullback_bracket_from_operator_envelope_operatorSubmodule) :
    D.pullback_bracket_from_operator_envelope_operatorBracket A (B₁ + B₂) =
      D.pullback_bracket_from_operator_envelope_operatorBracket A B₁ +
        D.pullback_bracket_from_operator_envelope_operatorBracket A B₂ := by
  apply Subtype.ext
  simp [pullback_bracket_from_operator_envelope_operatorBracket, sub_eq_add_neg, add_mul, mul_add]
  abel_nf

lemma pullback_bracket_from_operator_envelope_operatorBracket_antisymm
    (D : PullbackBracketFromOperatorEnvelopeData)
    (A B : D.pullback_bracket_from_operator_envelope_operatorSubmodule) :
    D.pullback_bracket_from_operator_envelope_operatorBracket A B =
      -D.pullback_bracket_from_operator_envelope_operatorBracket B A := by
  apply Subtype.ext
  simp [pullback_bracket_from_operator_envelope_operatorBracket, sub_eq_add_neg]

lemma pullback_bracket_from_operator_envelope_operatorBracket_jacobi
    (D : PullbackBracketFromOperatorEnvelopeData)
    (A B C : D.pullback_bracket_from_operator_envelope_operatorSubmodule) :
    D.pullback_bracket_from_operator_envelope_operatorBracket A
        (D.pullback_bracket_from_operator_envelope_operatorBracket B C) +
      D.pullback_bracket_from_operator_envelope_operatorBracket B
        (D.pullback_bracket_from_operator_envelope_operatorBracket C A) +
      D.pullback_bracket_from_operator_envelope_operatorBracket C
        (D.pullback_bracket_from_operator_envelope_operatorBracket A B) = 0 := by
  apply Subtype.ext
  simp [pullback_bracket_from_operator_envelope_operatorBracket]
  noncomm_ring

/-- The transported bracket intertwines with `Phi`, is additive in each argument, is
antisymmetric, and satisfies the Jacobi identity after pushing the cyclic sum through `Phi`. -/
def is_lie_pullback (D : PullbackBracketFromOperatorEnvelopeData) : Prop :=
  (∀ x y,
    D.pullback_bracket_from_operator_envelope_Phi
        (D.pullback_bracket_from_operator_envelope_bracket x y) =
      D.pullback_bracket_from_operator_envelope_operatorBracket
        (D.pullback_bracket_from_operator_envelope_Phi x)
        (D.pullback_bracket_from_operator_envelope_Phi y)) ∧
    (∀ x₁ x₂ y,
      D.pullback_bracket_from_operator_envelope_Phi
          (D.pullback_bracket_from_operator_envelope_bracket (x₁ + x₂) y) =
        D.pullback_bracket_from_operator_envelope_Phi
            (D.pullback_bracket_from_operator_envelope_bracket x₁ y) +
          D.pullback_bracket_from_operator_envelope_Phi
            (D.pullback_bracket_from_operator_envelope_bracket x₂ y)) ∧
    (∀ x y₁ y₂,
      D.pullback_bracket_from_operator_envelope_Phi
          (D.pullback_bracket_from_operator_envelope_bracket x (y₁ + y₂)) =
        D.pullback_bracket_from_operator_envelope_Phi
            (D.pullback_bracket_from_operator_envelope_bracket x y₁) +
          D.pullback_bracket_from_operator_envelope_Phi
            (D.pullback_bracket_from_operator_envelope_bracket x y₂)) ∧
    (∀ x y,
      D.pullback_bracket_from_operator_envelope_Phi
          (D.pullback_bracket_from_operator_envelope_bracket x y) =
        -D.pullback_bracket_from_operator_envelope_Phi
            (D.pullback_bracket_from_operator_envelope_bracket y x)) ∧
    ∀ x y z,
      D.pullback_bracket_from_operator_envelope_Phi
          (D.pullback_bracket_from_operator_envelope_bracket x
              (D.pullback_bracket_from_operator_envelope_bracket y z) +
            D.pullback_bracket_from_operator_envelope_bracket y
              (D.pullback_bracket_from_operator_envelope_bracket z x) +
            D.pullback_bracket_from_operator_envelope_bracket z
              (D.pullback_bracket_from_operator_envelope_bracket x y)) = 0

end PullbackBracketFromOperatorEnvelopeData

/-- Paper label: `thm:pullback-bracket-from-operator-envelope`. Transporting the operator
commutator along a `ℤ`-linear equivalence yields a Lie bracket on the source object. -/
theorem paper_pullback_bracket_from_operator_envelope
    (D : PullbackBracketFromOperatorEnvelopeData) : D.is_lie_pullback := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    simp [PullbackBracketFromOperatorEnvelopeData.pullback_bracket_from_operator_envelope_bracket]
  · intro x₁ x₂ y
    simpa [PullbackBracketFromOperatorEnvelopeData.pullback_bracket_from_operator_envelope_bracket,
      D.pullback_bracket_from_operator_envelope_Phi.map_add] using
      PullbackBracketFromOperatorEnvelopeData.pullback_bracket_from_operator_envelope_operatorBracket_add_left
        D
        (D.pullback_bracket_from_operator_envelope_Phi x₁)
        (D.pullback_bracket_from_operator_envelope_Phi x₂)
        (D.pullback_bracket_from_operator_envelope_Phi y)
  · intro x y₁ y₂
    simpa [PullbackBracketFromOperatorEnvelopeData.pullback_bracket_from_operator_envelope_bracket,
      D.pullback_bracket_from_operator_envelope_Phi.map_add] using
      PullbackBracketFromOperatorEnvelopeData.pullback_bracket_from_operator_envelope_operatorBracket_add_right
        D
        (D.pullback_bracket_from_operator_envelope_Phi x)
        (D.pullback_bracket_from_operator_envelope_Phi y₁)
        (D.pullback_bracket_from_operator_envelope_Phi y₂)
  · intro x y
    simpa [PullbackBracketFromOperatorEnvelopeData.pullback_bracket_from_operator_envelope_bracket] using
      PullbackBracketFromOperatorEnvelopeData.pullback_bracket_from_operator_envelope_operatorBracket_antisymm
        D
        (D.pullback_bracket_from_operator_envelope_Phi x)
        (D.pullback_bracket_from_operator_envelope_Phi y)
  · intro x y z
    simpa [PullbackBracketFromOperatorEnvelopeData.pullback_bracket_from_operator_envelope_bracket] using
      (PullbackBracketFromOperatorEnvelopeData.pullback_bracket_from_operator_envelope_operatorBracket_jacobi
        D
        (D.pullback_bracket_from_operator_envelope_Phi x)
        (D.pullback_bracket_from_operator_envelope_Phi y)
        (D.pullback_bracket_from_operator_envelope_Phi z))

end Omega.GroupUnification
