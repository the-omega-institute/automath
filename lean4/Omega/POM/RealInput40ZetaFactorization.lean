import Mathlib.Tactic
import Omega.EA.GlobalAssemblyZeta
import Omega.Graph.TransferMatrix

namespace Omega.POM

open Polynomial
open Omega.EA
open Omega.Graph

noncomputable section

/-- The golden skeleton used in the real-input `40` determinant factorization. -/
abbrev realInput40GoldenSkeletonA : Matrix (Fin 2) (Fin 2) ℤ :=
  goldenMeanAdjacency

/-- The tensor block coming from the golden skeleton. -/
abbrev realInput40TensorBlock : Matrix (Fin 2) (Fin 2) ℤ :=
  globalAssemblyK21Adjacency

/-- The sign-twisted golden skeleton. -/
abbrev realInput40TwistedSkeletonA : Matrix (Fin 2) (Fin 2) ℤ :=
  -realInput40GoldenSkeletonA

/-- The explicit determinant polynomial of the real-input `40` kernel in the `z`-variable. -/
def realInput40DetPolynomial : ℚ[X] :=
  (((1 : ℚ[X]) - Polynomial.X) ^ 2) * (((1 : ℚ[X]) + Polynomial.X) ^ 3) *
    (((1 : ℚ[X]) - Polynomial.C (3 : ℚ) * Polynomial.X) + Polynomial.X ^ 2) *
      (((1 : ℚ[X]) + Polynomial.X) - Polynomial.X ^ 2)

/-- The audited tensor-block determinant `det(I - z (A ⊗ A))`. -/
def realInput40TensorDetPolynomial : ℚ[X] :=
  (((1 : ℚ[X]) + Polynomial.X) ^ 2) *
    (((1 : ℚ[X]) - Polynomial.C (3 : ℚ) * Polynomial.X) + Polynomial.X ^ 2)

/-- The audited sign-twisted determinant `det(I - z (-A)) = det(I + z A)`. -/
def realInput40TwistedDetPolynomial : ℚ[X] :=
  ((1 : ℚ[X]) + Polynomial.X) - Polynomial.X ^ 2

/-- The trivial short-period determinant factor. -/
def realInput40TrivialPeriodDetPolynomial : ℚ[X] :=
  (((1 : ℚ[X]) - Polynomial.X) ^ 2) * ((1 : ℚ[X]) + Polynomial.X)

/-- The same short-period factor written in primitive Euler-product form. -/
def realInput40TrivialPrimitiveEulerPolynomial : ℚ[X] :=
  ((1 : ℚ[X]) - Polynomial.X) * ((1 : ℚ[X]) - Polynomial.X ^ 2)

/-- The primitive-orbit correction contributed by the trivial short-period factor. -/
def realInput40ShortPeriodPrimitiveContribution (n : ℕ) : ℚ :=
  if n = 1 then 1 else if n = 2 then 1 else 0

/-- Determinant-level factorization from the golden tensor block, the twisted `-A` block, and the
short-period correction. -/
def realInput40DetFactorization : Prop :=
  realInput40DetPolynomial =
    realInput40TrivialPeriodDetPolynomial *
      realInput40TensorDetPolynomial * realInput40TwistedDetPolynomial

/-- Zeta factorization written as an inverse-denominator identity. -/
def realInput40ZetaFactorization : Prop :=
  ∀ z : ℚ,
    Polynomial.eval z realInput40DetPolynomial ≠ 0 →
      Polynomial.eval z realInput40TrivialPeriodDetPolynomial ≠ 0 →
      Polynomial.eval z realInput40TensorDetPolynomial ≠ 0 →
      Polynomial.eval z realInput40TwistedDetPolynomial ≠ 0 →
      (1 / Polynomial.eval z realInput40DetPolynomial : ℚ) =
        (1 / Polynomial.eval z realInput40TensorDetPolynomial) *
          (1 / Polynomial.eval z realInput40TwistedDetPolynomial) *
            (1 / Polynomial.eval z realInput40TrivialPeriodDetPolynomial)

/-- The short-period correction only contributes primitive Euler factors in lengths `1` and `2`. -/
def realInput40ShortPeriodCorrection : Prop :=
  realInput40TrivialPeriodDetPolynomial = realInput40TrivialPrimitiveEulerPolynomial ∧
    ∀ n : ℕ, realInput40ShortPeriodPrimitiveContribution n ≠ 0 ↔ n = 1 ∨ n = 2

private lemma realInput40_det_factorization :
    realInput40DetFactorization := by
  dsimp [realInput40DetFactorization, realInput40DetPolynomial, realInput40TrivialPeriodDetPolynomial,
    realInput40TensorDetPolynomial, realInput40TwistedDetPolynomial]
  ring_nf

private lemma realInput40_zeta_factorization :
    realInput40ZetaFactorization := by
  intro z hdet htriv htensor htwisted
  have hfac := realInput40_det_factorization
  have hEval :
      Polynomial.eval z realInput40DetPolynomial =
        Polynomial.eval z realInput40TrivialPeriodDetPolynomial *
          Polynomial.eval z realInput40TensorDetPolynomial *
            Polynomial.eval z realInput40TwistedDetPolynomial := by
    simpa [realInput40DetFactorization] using congrArg (Polynomial.eval z) hfac
  rw [hEval]
  field_simp [htriv, htensor, htwisted]

private lemma realInput40_short_period_support :
    realInput40ShortPeriodCorrection := by
  refine ⟨?_, ?_⟩
  · dsimp [realInput40TrivialPeriodDetPolynomial, realInput40TrivialPrimitiveEulerPolynomial]
    ring_nf
  · intro n
    by_cases h1 : n = 1
    · subst h1
      simp [realInput40ShortPeriodPrimitiveContribution]
    · by_cases h2 : n = 2
      · subst h2
        simp [realInput40ShortPeriodPrimitiveContribution]
      · simp [realInput40ShortPeriodPrimitiveContribution, h1, h2]

/-- Paper label: `prop:pom-zeta-factorization-40`.
The real-input `40` determinant splits as the golden tensor block times the twisted `-A` factor
times the trivial short-period factor; the inverse-denominator zeta identity follows, and the
short-period correction is supported exactly at primitive lengths `1` and `2`. -/
theorem paper_pom_zeta_factorization_40 :
    realInput40DetFactorization ∧
      realInput40ZetaFactorization ∧
      realInput40ShortPeriodCorrection := by
  exact ⟨realInput40_det_factorization, realInput40_zeta_factorization,
    realInput40_short_period_support⟩

end

end Omega.POM
