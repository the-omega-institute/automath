import Mathlib.Tactic
import Omega.Folding.BernoulliPRegenerationBivariatePGF

namespace Omega.Folding

/-- Concrete real data for the Bernoulli-`p` renewal/determinant factorization. The fields record
the cycle parameter together with the nonvanishing hypotheses needed for the rational identities
in the theorem. -/
structure BernoulliPRenewalDeterminantFactorizationData where
  p : ℝ
  u : ℝ
  z : ℝ
  hp : 0 < p
  hp1 : p < 1
  hzK : 1 - (1 - p) * z ≠ 0
  hzN : 1 - p * u * z ^ 2 ≠ 0
  hzSeries :
    1 - p * (u ^ 3 * z ^ 3 * ((1 - p) / (1 - p * u * z ^ 2)) * (p / (1 - (1 - p) * z))) ≠ 0
  hzClosed :
    (1 - (1 - p) * z) * (1 - p * u * z ^ 2) - p ^ 2 * (1 - p) * u ^ 3 * z ^ 3 ≠ 0
  hone :
    1 -
        (p * (1 - p) * z ^ 2 * (1 - p * u * z ^ 2)) /
          ((1 - (1 - p) * z) * (1 - p * u * z ^ 2) - p ^ 2 * (1 - p) * u ^ 3 * z ^ 3) ≠
      0
  hdet :
    ((1 - (1 - p) * z) * (1 - p * u * z ^ 2) - p ^ 2 * (1 - p) * u ^ 3 * z ^ 3) *
        (1 -
          (p * (1 - p) * z ^ 2 * (1 - p * u * z ^ 2)) /
            ((1 - (1 - p) * z) * (1 - p * u * z ^ 2) - p ^ 2 * (1 - p) * u ^ 3 * z ^ 3)) =
      ((1 - (1 - p) * z) * (1 - p * u * z ^ 2) - p ^ 2 * (1 - p) * u ^ 3 * z ^ 3) -
        p * (1 - p) * z ^ 2 * (1 - p * u * z ^ 2)

namespace BernoulliPRenewalDeterminantFactorizationData

/-- The denominator appearing in the closed form for the renewal kernel. -/
def denPhi (D : BernoulliPRenewalDeterminantFactorizationData) : ℝ :=
  (1 - (1 - D.p) * D.z) * (1 - D.p * D.u * D.z ^ 2) - D.p ^ 2 * (1 - D.p) * D.u ^ 3 * D.z ^ 3

/-- The explicit regeneration kernel `Φ_p(u,z)` in simplified rational form. -/
noncomputable def Phi (D : BernoulliPRenewalDeterminantFactorizationData) : ℝ :=
  (D.p * (1 - D.p) * D.z ^ 2 * (1 - D.p * D.u * D.z ^ 2)) / D.denPhi

/-- The explicit `Ψ_p(u,z)` numerator term from the renewal update. -/
noncomputable def Psi (D : BernoulliPRenewalDeterminantFactorizationData) : ℝ :=
  1 +
    D.z * (1 + D.p ^ 2 * D.u * D.z - D.p * D.u * D.z ^ 2 + D.p ^ 2 * D.u ^ 2 * D.z ^ 2) /
      D.denPhi

/-- The rational renewal solution `F = Ψ / (1 - Φ)`. -/
noncomputable def renewalF (D : BernoulliPRenewalDeterminantFactorizationData) : ℝ :=
  D.Psi / (1 - D.Phi)

/-- The determinant numerator obtained after clearing the `Φ` denominator. -/
noncomputable def detNumerator (D : BernoulliPRenewalDeterminantFactorizationData) : ℝ :=
  D.denPhi * (1 - D.Phi)

/-- The same polynomial viewed as the recurrence denominator. -/
def recurrenceDenominator (D : BernoulliPRenewalDeterminantFactorizationData) : ℝ :=
  D.denPhi - D.p * (1 - D.p) * D.z ^ 2 * (1 - D.p * D.u * D.z ^ 2)

/-- The strict renewal decomposition `F = Ψ + ΦF`. -/
def strictRenewalDecomposition (D : BernoulliPRenewalDeterminantFactorizationData) : Prop :=
  D.renewalF = D.Psi + D.Phi * D.renewalF

/-- The chosen `Ψ` is the explicit rational formula from the paper. -/
def explicitPsiFormula (D : BernoulliPRenewalDeterminantFactorizationData) : Prop :=
  D.Psi =
    1 +
      D.z * (1 + D.p ^ 2 * D.u * D.z - D.p * D.u * D.z ^ 2 + D.p ^ 2 * D.u ^ 2 * D.z ^ 2) /
        D.denPhi

/-- Clearing denominators identifies `1 - Φ` with the determinant numerator over `Den_Φ`. -/
def denominatorGeometrization (D : BernoulliPRenewalDeterminantFactorizationData) : Prop :=
  D.detNumerator = D.denPhi * (1 - D.Phi)

/-- The determinant numerator is exactly the recurrence denominator polynomial. -/
def detEqualsDenominator (D : BernoulliPRenewalDeterminantFactorizationData) : Prop :=
  D.detNumerator = D.recurrenceDenominator

end BernoulliPRenewalDeterminantFactorizationData

open BernoulliPRenewalDeterminantFactorizationData

/-- Paper label: `thm:fold-bernoulli-p-renewal-determinant-factorization`. -/
theorem paper_fold_bernoulli_p_renewal_determinant_factorization
    (D : BernoulliPRenewalDeterminantFactorizationData) :
    And D.strictRenewalDecomposition
      (And D.explicitPsiFormula (And D.denominatorGeometrization D.detEqualsDenominator)) := by
  have hcycle :
      bernoulliPRegenerationBivariatePGFViaCycles D.p D.u D.z =
        bernoulliPRegenerationBivariatePGFClosedForm D.p D.u D.z := by
    rcases
      paper_fold_bernoulli_p_regeneration_bivariate_pgf D.p D.u D.z D.hp D.hp1 D.hzK D.hzN
        D.hzSeries D.hzClosed with
      ⟨_, _, _, hclosed⟩
    exact hclosed
  have hone :
      1 - D.Phi ≠ 0 := by
    simpa [BernoulliPRenewalDeterminantFactorizationData.Phi] using D.hone
  have hclosed :
      D.denPhi ≠ 0 := by
    simpa [BernoulliPRenewalDeterminantFactorizationData.denPhi] using D.hzClosed
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold BernoulliPRenewalDeterminantFactorizationData.strictRenewalDecomposition
    unfold BernoulliPRenewalDeterminantFactorizationData.renewalF
    field_simp [BernoulliPRenewalDeterminantFactorizationData.Phi, hone]
    ring_nf
  · unfold BernoulliPRenewalDeterminantFactorizationData.explicitPsiFormula
    simpa [BernoulliPRenewalDeterminantFactorizationData.Psi]
  · unfold BernoulliPRenewalDeterminantFactorizationData.denominatorGeometrization
    rfl
  · unfold BernoulliPRenewalDeterminantFactorizationData.detEqualsDenominator
    unfold BernoulliPRenewalDeterminantFactorizationData.detNumerator
    unfold BernoulliPRenewalDeterminantFactorizationData.recurrenceDenominator
    unfold BernoulliPRenewalDeterminantFactorizationData.Phi
    unfold BernoulliPRenewalDeterminantFactorizationData.denPhi
    simpa using D.hdet

end Omega.Folding
