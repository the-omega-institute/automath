import Mathlib.Tactic

namespace Omega.POM

/-- Concrete parameter package for the explicit even-spectrum quintic of the `A₄(t)` family. -/
structure A4TEvenZetaQuinticData where
  t : ℤ

namespace A4TEvenZetaQuinticData

/-- The two quadratic factors appearing in the closed even-spectrum determinant factorization. -/
def evenFactorLeft (D : A4TEvenZetaQuinticData) (u : ℤ) : ℤ :=
  u ^ 2 + (D.t + 1) * u + 1

/-- The conjugate quadratic factor. -/
def evenFactorRight (D : A4TEvenZetaQuinticData) (u : ℤ) : ℤ :=
  u ^ 2 + (1 - D.t) * u + 1

/-- The explicit quintic obtained by expanding `- (u - 1) * evenFactorLeft * evenFactorRight`. -/
def evenQuintic (D : A4TEvenZetaQuinticData) (u : ℤ) : ℤ :=
  -u ^ 5 - u ^ 4 + (D.t ^ 2 - 1) * u ^ 3 + (1 - D.t ^ 2) * u ^ 2 + u + 1

/-- The discriminant factorization used to isolate the unique nonnegative degeneration point. -/
def discriminant (D : A4TEvenZetaQuinticData) : ℤ :=
  (D.t - 1) ^ 2 * (D.t ^ 2 + 1)

/-- Determinant identity for the explicit even-spectrum quintic. -/
def detMulNeg_eq_evenQuintic (D : A4TEvenZetaQuinticData) : Prop :=
  ∀ u : ℤ, -(u - 1) * (D.evenFactorLeft u * D.evenFactorRight u) = D.evenQuintic u

/-- On the nonnegative `t`-axis the discriminant vanishes only at `t = 1`. -/
def discNonzeroAwayFromOne (D : A4TEvenZetaQuinticData) : Prop :=
  0 ≤ D.t → D.t ≠ 1 → D.discriminant ≠ 0

lemma detMulNeg_eq_evenQuintic_holds (D : A4TEvenZetaQuinticData) : D.detMulNeg_eq_evenQuintic := by
  intro u
  dsimp [detMulNeg_eq_evenQuintic, evenFactorLeft, evenFactorRight, evenQuintic]
  ring

lemma positive_discriminant_tail (D : A4TEvenZetaQuinticData) (ht : 0 ≤ D.t) : 0 < D.t ^ 2 + 1 := by
  have ht' : 0 ≤ D.t := ht
  nlinarith [ht']

lemma discNonzeroAwayFromOne_holds (D : A4TEvenZetaQuinticData) : D.discNonzeroAwayFromOne := by
  intro ht hne
  have hsq : (D.t - 1) ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (sub_ne_zero.mpr hne)
  have htail : D.t ^ 2 + 1 ≠ 0 := by
    have hpos := D.positive_discriminant_tail ht
    linarith
  simpa [discriminant] using mul_ne_zero hsq htail

end A4TEvenZetaQuinticData

open A4TEvenZetaQuinticData

/-- Paper label: `prop:pom-a4t-even-zeta-quintic`. The explicit even-spectrum determinant factors
through two quadratic terms, and the displayed discriminant factorization leaves `t = 1` as the
only nonnegative degeneration point. -/
theorem paper_pom_a4t_even_zeta_quintic (D : A4TEvenZetaQuinticData) :
    D.detMulNeg_eq_evenQuintic ∧ D.discNonzeroAwayFromOne := by
  exact ⟨D.detMulNeg_eq_evenQuintic_holds, D.discNonzeroAwayFromOne_holds⟩

end Omega.POM
