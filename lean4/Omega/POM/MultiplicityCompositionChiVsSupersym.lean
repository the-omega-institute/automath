import Mathlib.Tactic

namespace Omega.POM

open Filter

/-- Concrete main-term data for
`cor:pom-multiplicity-composition-chi-vs-supersym`.

The three asymptotic inputs are represented as eventual exact main-term identities for the
supersymmetric layer and the two negative chi-anomaly events. -/
structure pom_multiplicity_composition_chi_vs_supersym_data where
  supersymProb : ℕ → ℝ
  cNegativeProb : ℕ → ℝ
  iNegativeProb : ℕ → ℝ
  lambdaRatio : ℝ
  mu1 : ℝ
  mu0 : ℝ
  cConstant : ℝ
  iConstant : ℝ
  lambdaRatio_ne_zero : lambdaRatio ≠ 0
  mu1_ne_zero : mu1 ≠ 0
  mu0_ne_zero : mu0 ≠ 0
  supersym_asymptotic :
    ∀ᶠ L in atTop, supersymProb L = (mu1 / mu0) * lambdaRatio ^ L
  c_negative_asymptotic :
    ∀ᶠ L in atTop,
      cNegativeProb L = (mu1 * cConstant / mu0 ^ 2) * (L : ℝ) * lambdaRatio ^ L
  i_negative_asymptotic :
    ∀ᶠ L in atTop,
      iNegativeProb L = (mu1 * iConstant / mu0 ^ 2) * (L : ℝ) * lambdaRatio ^ L

namespace pom_multiplicity_composition_chi_vs_supersym_data

/-- The C-negative chi-anomaly layer is linear relative to the supersymmetric layer. -/
def c_negative_ratio_linear (D : pom_multiplicity_composition_chi_vs_supersym_data) :
    Prop :=
  ∀ᶠ L in atTop,
    D.cNegativeProb L / D.supersymProb L = (D.cConstant / D.mu0) * (L : ℝ)

/-- The iota-negative chi-anomaly layer is linear relative to the supersymmetric layer. -/
def i_negative_ratio_linear (D : pom_multiplicity_composition_chi_vs_supersym_data) :
    Prop :=
  ∀ᶠ L in atTop,
    D.iNegativeProb L / D.supersymProb L = (D.iConstant / D.mu0) * (L : ℝ)

end pom_multiplicity_composition_chi_vs_supersym_data

/-- Paper label: `cor:pom-multiplicity-composition-chi-vs-supersym`. -/
theorem paper_pom_multiplicity_composition_chi_vs_supersym
    (D : pom_multiplicity_composition_chi_vs_supersym_data) :
    D.c_negative_ratio_linear ∧ D.i_negative_ratio_linear := by
  constructor
  · filter_upwards [D.supersym_asymptotic, D.c_negative_asymptotic] with L hsup hc
    rw [hc, hsup]
    have hlambda : D.lambdaRatio ^ L ≠ 0 := pow_ne_zero L D.lambdaRatio_ne_zero
    have hden : (D.mu1 / D.mu0) * D.lambdaRatio ^ L ≠ 0 :=
      mul_ne_zero (div_ne_zero D.mu1_ne_zero D.mu0_ne_zero) hlambda
    field_simp [hden, D.mu0_ne_zero, D.mu1_ne_zero, hlambda]
  · filter_upwards [D.supersym_asymptotic, D.i_negative_asymptotic] with L hsup hi
    rw [hi, hsup]
    have hlambda : D.lambdaRatio ^ L ≠ 0 := pow_ne_zero L D.lambdaRatio_ne_zero
    have hden : (D.mu1 / D.mu0) * D.lambdaRatio ^ L ≠ 0 :=
      mul_ne_zero (div_ne_zero D.mu1_ne_zero D.mu0_ne_zero) hlambda
    field_simp [hden, D.mu0_ne_zero, D.mu1_ne_zero, hlambda]

end Omega.POM
