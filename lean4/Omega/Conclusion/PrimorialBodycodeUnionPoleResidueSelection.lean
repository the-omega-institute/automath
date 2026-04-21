import Mathlib
import Omega.Conclusion.PrimorialBodycodePoleResidueInversion

namespace Omega.Conclusion

/-- The dominant pole attached to a growth exponent `d` in ambient dimension `n`. -/
def primorialBodycodePole (n d : ℕ) : ℕ :=
  n - d

/-- The pole selected by the dominant exponent in a disjoint union. -/
def primorialBodycodeUnionPole (n d₁ d₂ : ℕ) : ℕ :=
  primorialBodycodePole n (max d₁ d₂)

/-- The residue of the union: equal exponents add, otherwise the larger exponent dominates. -/
def primorialBodycodeUnionResidue (d₁ d₂ : ℕ) (R₁ R₂ : ℝ) : ℝ :=
  if d₁ = d₂ then R₁ + R₂ else if d₂ < d₁ then R₁ else R₂

/-- Paper label: `thm:conclusion-primorial-bodycode-union-pole-residue-selection`.

The dominant pole is read from the larger exponent, while equal exponents contribute additively to
the leading residue. -/
theorem paper_conclusion_primorial_bodycode_union_pole_residue_selection
    (n d₁ d₂ : ℕ) (R₁ R₂ : ℝ) :
    (d₁ > d₂ →
      primorialBodycodeUnionPole n d₁ d₂ = primorialBodycodePole n d₁ ∧
        primorialBodycodeUnionResidue d₁ d₂ R₁ R₂ = R₁) ∧
      (d₁ = d₂ →
        primorialBodycodeUnionPole n d₁ d₂ = primorialBodycodePole n d₁ ∧
          primorialBodycodeUnionResidue d₁ d₂ R₁ R₂ = R₁ + R₂) := by
  constructor
  · intro hlt
    constructor
    · unfold primorialBodycodeUnionPole primorialBodycodePole
      rw [Nat.max_eq_left (le_of_lt hlt)]
    · unfold primorialBodycodeUnionResidue
      simp [Nat.ne_of_gt hlt, hlt]
  · intro heq
    constructor
    · simp [primorialBodycodeUnionPole, primorialBodycodePole, heq]
    · simp [primorialBodycodeUnionResidue, heq]

end Omega.Conclusion
