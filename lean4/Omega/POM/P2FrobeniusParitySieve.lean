import Mathlib.Tactic

namespace Omega.POM

/-- The three conjugacy classes of `S₃`, identified with the three unramified factorization types
for a cubic polynomial modulo a prime. -/
inductive P2S3FrobeniusClass where
  | identity
  | transposition
  | threeCycle
  deriving DecidableEq, Repr

/-- The `S₃` class size attached to an unramified Frobenius class. -/
def p2S3ClassSize : P2S3FrobeniusClass → ℕ
  | .identity => 1
  | .transposition => 3
  | .threeCycle => 2

/-- The quadratic subfield `ℚ(√37)` records the Frobenius parity through the sign character. -/
def p2QuadraticSubfieldLegendre37 : P2S3FrobeniusClass → ℤ
  | .identity => 1
  | .transposition => -1
  | .threeCycle => 1

/-- Frobenius parity as the sign character on `S₃`. -/
def p2FrobeniusParitySign : P2S3FrobeniusClass → ℤ :=
  p2QuadraticSubfieldLegendre37

/-- The corresponding factorization degrees of `P₂ mod p`. -/
def p2FactorizationDegrees : P2S3FrobeniusClass → List ℕ
  | .identity => [1, 1, 1]
  | .transposition => [1, 2]
  | .threeCycle => [3]

/-- The raw Chebotarev numerator is the class size. -/
def p2RawDensityNumerator : P2S3FrobeniusClass → ℕ :=
  p2S3ClassSize

/-- The raw Chebotarev denominator is `|S₃| = 6`. -/
def p2RawDensityDenominator : ℕ := 6

/-- Conditional numerators inside the quadratic-residue (`(37/p)=1`) sector. -/
def p2ResidueConditionalNumerator : P2S3FrobeniusClass → ℕ
  | .identity => 1
  | .transposition => 0
  | .threeCycle => 2

/-- Conditional numerators inside the quadratic-nonresidue (`(37/p)=-1`) sector. -/
def p2NonresidueConditionalNumerator : P2S3FrobeniusClass → ℕ
  | .identity => 0
  | .transposition => 3
  | .threeCycle => 0

/-- The conditional denominator on either parity side is `3`. -/
def p2ResidueConditionalDenominator : ℕ := 3

/-- The conditional denominator on either parity side is `3`. -/
def p2NonresidueConditionalDenominator : ℕ := 3

/-- The `S₃` class sizes sum to `6`. -/
theorem p2_s3_class_sizes_sum :
    p2S3ClassSize .identity + p2S3ClassSize .transposition + p2S3ClassSize .threeCycle = 6 := by
  native_decide

/-- The quadratic subfield `ℚ(√37)` identifies Frobenius parity via the sign character, and the
three `S₃` conjugacy classes recover the factorization types together with their raw and
conditional Chebotarev numerators/denominators.
    prop:pom-p2-frobenius-parity-sieve -/
theorem paper_pom_p2_frobenius_parity_sieve :
    (∀ C, p2QuadraticSubfieldLegendre37 C = p2FrobeniusParitySign C) ∧
      p2FactorizationDegrees .identity = [1, 1, 1] ∧
      p2FactorizationDegrees .transposition = [1, 2] ∧
      p2FactorizationDegrees .threeCycle = [3] ∧
      (∀ C, p2RawDensityNumerator C = p2S3ClassSize C ∧ p2RawDensityDenominator = 6) ∧
      (∀ C, p2QuadraticSubfieldLegendre37 C = 1 →
        p2ResidueConditionalNumerator C =
          if C = .identity then 1 else if C = .threeCycle then 2 else 0) ∧
      p2ResidueConditionalDenominator = 3 ∧
      (∀ C, p2QuadraticSubfieldLegendre37 C = -1 →
        p2NonresidueConditionalNumerator C =
          if C = .transposition then 3 else 0) ∧
      p2NonresidueConditionalDenominator = 3 := by
  refine ⟨fun C => rfl, rfl, rfl, rfl, ?_, ?_, rfl, ?_, rfl⟩
  · intro C
    exact ⟨rfl, rfl⟩
  · intro C hC
    cases C <;> simp [p2QuadraticSubfieldLegendre37, p2ResidueConditionalNumerator] at hC ⊢
  · intro C hC
    cases C <;> simp [p2QuadraticSubfieldLegendre37, p2NonresidueConditionalNumerator] at hC ⊢

end Omega.POM
