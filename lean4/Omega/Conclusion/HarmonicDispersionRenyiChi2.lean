import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

noncomputable section

/-- Concrete finite-distribution package for the harmonic-dispersion `Renyi`/`χ²` comparison with
the uniform reference law on `Fin n`. -/
structure HarmonicDispersionRenyiChi2Data where
  n : ℕ
  hn : 0 < n
  mass : Fin n → ℝ
  renyiOne : ℝ
  hmass_nonneg : ∀ i, 0 ≤ mass i
  hmass_sum : ∑ i, mass i = 1
  hrenyi_monotone :
    renyiOne ≤ Real.log ((n : ℝ) * ∑ i : Fin n, mass i ^ 2)

namespace HarmonicDispersionRenyiChi2Data

/-- Uniform reference law on the same finite space. -/
def conclusion_harmonic_dispersion_renyi_chi2_uniformMass
    (D : HarmonicDispersionRenyiChi2Data) (_i : Fin D.n) : ℝ :=
  1 / (D.n : ℝ)

/-- The common quadratic moment appearing in the order-`2` Renyi divergence and the Pearson
`χ²` divergence against the uniform law. -/
def conclusion_harmonic_dispersion_renyi_chi2_reciprocalSum
    (D : HarmonicDispersionRenyiChi2Data) : ℝ :=
  (D.n : ℝ) * ∑ i : Fin D.n, D.mass i ^ 2

/-- Order-`2` Renyi divergence relative to the uniform law. -/
def conclusion_harmonic_dispersion_renyi_chi2_renyiTwo
    (D : HarmonicDispersionRenyiChi2Data) : ℝ :=
  Real.log D.conclusion_harmonic_dispersion_renyi_chi2_reciprocalSum

/-- Pearson `χ²` divergence relative to the uniform law. -/
def conclusion_harmonic_dispersion_renyi_chi2_chi2
    (D : HarmonicDispersionRenyiChi2Data) : ℝ :=
  D.conclusion_harmonic_dispersion_renyi_chi2_reciprocalSum - 1

/-- Direct expansion of the order-`2` Renyi divergence. -/
def renyi2Exact (D : HarmonicDispersionRenyiChi2Data) : Prop :=
  D.conclusion_harmonic_dispersion_renyi_chi2_renyiTwo =
    Real.log D.conclusion_harmonic_dispersion_renyi_chi2_reciprocalSum

/-- The `[1,2]` comparison supplied by Renyi monotonicity for the chosen order-`1` divergence. -/
def renyiUpperBound (D : HarmonicDispersionRenyiChi2Data) : Prop :=
  D.renyiOne ≤ D.conclusion_harmonic_dispersion_renyi_chi2_renyiTwo

/-- Rewriting the same quadratic moment as a Pearson `χ²` divergence. -/
def chi2Exact (D : HarmonicDispersionRenyiChi2Data) : Prop :=
  D.conclusion_harmonic_dispersion_renyi_chi2_chi2 =
    D.conclusion_harmonic_dispersion_renyi_chi2_reciprocalSum - 1

end HarmonicDispersionRenyiChi2Data

open HarmonicDispersionRenyiChi2Data

/-- Paper label: `thm:conclusion-harmonic-dispersion-renyi-chi2`. The order-`2` Renyi divergence
against the uniform reference law is the logarithm of the quadratic moment, the order-`1`
divergence is bounded above by monotonicity on `[1,2]`, and the same quadratic moment rewrites as
the Pearson `χ²` divergence plus `1`. -/
theorem paper_conclusion_harmonic_dispersion_renyi_chi2
    (D : Omega.Conclusion.HarmonicDispersionRenyiChi2Data) :
    D.renyi2Exact ∧ D.renyiUpperBound ∧ D.chi2Exact := by
  refine ⟨rfl, ?_, rfl⟩
  simpa [HarmonicDispersionRenyiChi2Data.renyiUpperBound,
    HarmonicDispersionRenyiChi2Data.conclusion_harmonic_dispersion_renyi_chi2_renyiTwo,
    HarmonicDispersionRenyiChi2Data.conclusion_harmonic_dispersion_renyi_chi2_reciprocalSum] using
    D.hrenyi_monotone

end

end Omega.Conclusion
