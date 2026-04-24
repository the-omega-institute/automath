import Omega.POM.OracleCapacityKolmogorovSpectrum

namespace Omega.POM

open scoped BigOperators

universe u

/-- Paper label: `thm:derived-kolmogorov-oracle-exponent-isomorphism`.
The aggregate oracle/Kolmogorov sandwich gives a uniform constant-shift comparison on counts, and
any thermal-cut and differential identities already known for the oracle exponent transfer
verbatim once the Kolmogorov exponent is identified with it at the chosen energy. -/
theorem paper_derived_kolmogorov_oracle_exponent_isomorphism
    {X : Type u} [Fintype X]
    (fiberCardinality : X → ℕ) (kolmogorovCount : X → ℕ → ℕ)
    (hContainment : ∀ x B, kolmogorovCount x B ≤ fiberCardinality x)
    (hPointwise : ∀ x B, kolmogorovCount x B ≤ 2 ^ B)
    (hCoverage : ∃ c, ∀ x B, Nat.min (fiberCardinality x) (2 ^ B) ≤ kolmogorovCount x (B + c))
    (oracleExponent kolmogorovExponent thermalProfile qStar tauTwo tauThree oracleSlope
      oracleCurvature oracleTorsion kolmogorovSlope kolmogorovCurvature
      kolmogorovTorsion : ℝ → ℝ)
    (a : ℝ)
    (hExponentIso : kolmogorovExponent a = oracleExponent a)
    (hThermalCut : oracleExponent a = thermalProfile a + a)
    (hOracleSlope : oracleSlope a = 1 - qStar a)
    (hOracleCurvature : oracleCurvature a = -(1 / tauTwo a))
    (hOracleTorsion : oracleTorsion a = tauThree a / (tauTwo a) ^ 3)
    (hSlopeTransfer : kolmogorovSlope a = oracleSlope a)
    (hCurvatureTransfer : kolmogorovCurvature a = oracleCurvature a)
    (hTorsionTransfer : kolmogorovTorsion a = oracleTorsion a) :
    ∃ c : ℕ,
      (∀ B,
        (∑ x, Nat.min (fiberCardinality x) (2 ^ B)) ≤ ∑ x, kolmogorovCount x (B + c) ∧
          (∑ x, kolmogorovCount x (B + c)) ≤
            2 ^ c * ∑ x, Nat.min (fiberCardinality x) (2 ^ B)) ∧
      kolmogorovExponent a = oracleExponent a ∧
      kolmogorovExponent a = thermalProfile a + a ∧
      kolmogorovSlope a = 1 - qStar a ∧
      kolmogorovCurvature a = -(1 / tauTwo a) ∧
      kolmogorovTorsion a = tauThree a / (tauTwo a) ^ 3 := by
  let D : OracleCapacityKolmogorovSpectrumData :=
    { X := X
      instFintypeX := inferInstance
      fiberCardinality := fiberCardinality
      kolmogorovCount := kolmogorovCount
      fiberContainment := hContainment }
  rcases paper_pom_oracle_capacity_kolmogorov_spectrum D hPointwise hCoverage with ⟨c, hc⟩
  refine ⟨c, hc, hExponentIso, ?_, ?_, ?_, ?_⟩
  · calc
      kolmogorovExponent a = oracleExponent a := hExponentIso
      _ = thermalProfile a + a := hThermalCut
  · calc
      kolmogorovSlope a = oracleSlope a := hSlopeTransfer
      _ = 1 - qStar a := hOracleSlope
  · calc
      kolmogorovCurvature a = oracleCurvature a := hCurvatureTransfer
      _ = -(1 / tauTwo a) := hOracleCurvature
  · calc
      kolmogorovTorsion a = oracleTorsion a := hTorsionTransfer
      _ = tauThree a / (tauTwo a) ^ 3 := hOracleTorsion

end Omega.POM
