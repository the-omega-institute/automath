import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyGcDefectFarfieldExpansion

namespace Omega.Folding

open Real

/-- The Perron root coming from the matching sector in the Bernoulli-`p` GC-defect model. -/
noncomputable def bernoulliPGcAlpha (p : ℝ) : ℝ :=
  (1 - p + Real.sqrt ((1 - p) * (1 + 3 * p))) / 2

/-- The asymptotic three-cycle mismatch weight. -/
noncomputable def bernoulliPMismatch3CycleWeight (p : ℝ) : ℝ :=
  p ^ 2 * (1 - p)

/-- The explicit positive-side far-field logarithmic balance. -/
noncomputable def bernoulliPGcPositiveFarfieldBalance (p : ℝ) : ℝ :=
  Real.log (bernoulliPMismatch3CycleWeight p / bernoulliPGcAlpha p ^ 3)

/-- The negative-side balance is the opposite of the positive-side balance. -/
noncomputable def bernoulliPGcNegativeFarfieldBalance (p : ℝ) : ℝ :=
  -bernoulliPGcPositiveFarfieldBalance p

/-- A concrete odd profile used to package the GC-defect symmetry. -/
noncomputable def bernoulliPGcOddProfile (θ : ℝ) : ℝ :=
  θ / (1 + |θ|)

/-- A concrete odd GC-defect representative with the prescribed far-field constants. -/
noncomputable def bernoulliPGcDefect (p θ : ℝ) : ℝ :=
  bernoulliPGcPositiveFarfieldBalance p * bernoulliPGcOddProfile θ

/-- The critical polynomial obtained after eliminating the square root from the zero-locus
equation. -/
noncomputable def bernoulliPGcCriticalPolynomial (p : ℝ) : ℝ :=
  4 * p ^ 2 - 2 * p - 1

private lemma bernoulliPGcOddProfile_neg (θ : ℝ) :
    bernoulliPGcOddProfile (-θ) = -bernoulliPGcOddProfile θ := by
  unfold bernoulliPGcOddProfile
  rw [abs_neg]
  ring

private lemma bernoulliPGcAlpha_pos {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    0 < bernoulliPGcAlpha p := by
  unfold bernoulliPGcAlpha
  have hdisc_nonneg : 0 ≤ (1 - p) * (1 + 3 * p) := by
    nlinarith
  have hbase : 0 < 1 - p := by linarith
  have hsqrt_nonneg : 0 ≤ Real.sqrt ((1 - p) * (1 + 3 * p)) := Real.sqrt_nonneg _
  nlinarith

private lemma bernoulliPGcAlpha_quadratic {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    bernoulliPGcAlpha p ^ 2 = (1 - p) * bernoulliPGcAlpha p + p * (1 - p) := by
  unfold bernoulliPGcAlpha
  have hdisc_nonneg : 0 ≤ (1 - p) * (1 + 3 * p) := by
    nlinarith
  have hsqrt_sq : Real.sqrt ((1 - p) * (1 + 3 * p)) ^ 2 = (1 - p) * (1 + 3 * p) := by
    rw [Real.sq_sqrt hdisc_nonneg]
  field_simp
  ring_nf at hsqrt_sq ⊢
  nlinarith

private lemma bernoulliPGcPoly_zero_iff_root {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    bernoulliPGcCriticalPolynomial p = 0 ↔ p = (1 + Real.sqrt 5) / 4 := by
  constructor
  · intro hpoly
    have hsq : (4 * p - 1) ^ 2 = 5 := by
      unfold bernoulliPGcCriticalPolynomial at hpoly
      nlinarith
    have hnonneg : 0 ≤ 4 * p - 1 := by
      unfold bernoulliPGcCriticalPolynomial at hpoly
      nlinarith
    have hsqrt_sq : (Real.sqrt 5) ^ 2 = 5 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
    nlinarith [hsq, hsqrt_sq, hnonneg, Real.sqrt_nonneg 5]
  · intro hp_eq
    unfold bernoulliPGcCriticalPolynomial
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]

private lemma bernoulliPGcFarfield_zero_of_poly_zero {p : ℝ}
    (hp : 0 < p) (_hp' : p < 1) (hpoly : bernoulliPGcCriticalPolynomial p = 0) :
    bernoulliPGcPositiveFarfieldBalance p = 0 := by
  have hdisc : (1 - p) * (1 + 3 * p) = p ^ 2 := by
    unfold bernoulliPGcCriticalPolynomial at hpoly
    nlinarith
  have hsqrt : Real.sqrt ((1 - p) * (1 + 3 * p)) = p := by
    rw [hdisc, Real.sqrt_sq hp.le]
  have halpha : bernoulliPGcAlpha p = 1 / 2 := by
    unfold bernoulliPGcAlpha
    rw [hsqrt]
    ring
  have hmismatch : bernoulliPMismatch3CycleWeight p = 1 / 8 := by
    unfold bernoulliPMismatch3CycleWeight bernoulliPGcCriticalPolynomial at *
    nlinarith
  unfold bernoulliPGcPositiveFarfieldBalance
  rw [hmismatch, halpha]
  norm_num

private lemma bernoulliPGcPoly_zero_of_farfield_zero {p : ℝ}
    (hp : 0 < p) (hp' : p < 1) (hbal : bernoulliPGcPositiveFarfieldBalance p = 0) :
    bernoulliPGcCriticalPolynomial p = 0 := by
  have hαpos : 0 < bernoulliPGcAlpha p := bernoulliPGcAlpha_pos hp hp'
  have hmismatch_pos : 0 < bernoulliPMismatch3CycleWeight p := by
    unfold bernoulliPMismatch3CycleWeight
    have hp2 : 0 < p ^ 2 := by positivity
    have h1p : 0 < 1 - p := by linarith
    exact mul_pos hp2 h1p
  have hratio_pos :
      0 < bernoulliPMismatch3CycleWeight p / bernoulliPGcAlpha p ^ 3 := by
    have hαpow : 0 < bernoulliPGcAlpha p ^ 3 := by positivity
    exact div_pos hmismatch_pos hαpow
  have hratio :
      bernoulliPMismatch3CycleWeight p / bernoulliPGcAlpha p ^ 3 = 1 := by
    have hexp := congrArg Real.exp hbal
    simpa [bernoulliPGcPositiveFarfieldBalance, Real.exp_log hratio_pos] using hexp
  have hcrit : bernoulliPMismatch3CycleWeight p = bernoulliPGcAlpha p ^ 3 := by
    unfold bernoulliPMismatch3CycleWeight at *
    have hαpow_ne : bernoulliPGcAlpha p ^ 3 ≠ 0 := by positivity
    field_simp [hαpow_ne] at hratio
    exact hratio
  have hquad := bernoulliPGcAlpha_quadratic hp hp'
  have hcube :
      bernoulliPGcAlpha p ^ 3 = (1 - p) * bernoulliPGcAlpha p + p * (1 - p) ^ 2 := by
    calc
      bernoulliPGcAlpha p ^ 3 = bernoulliPGcAlpha p * bernoulliPGcAlpha p ^ 2 := by ring
      _ = bernoulliPGcAlpha p * ((1 - p) * bernoulliPGcAlpha p + p * (1 - p)) := by
            rw [hquad]
      _ = (1 - p) * bernoulliPGcAlpha p ^ 2 + p * (1 - p) * bernoulliPGcAlpha p := by ring
      _ = (1 - p) * ((1 - p) * bernoulliPGcAlpha p + p * (1 - p)) +
            p * (1 - p) * bernoulliPGcAlpha p := by rw [hquad]
      _ = (1 - p) * bernoulliPGcAlpha p + p * (1 - p) ^ 2 := by ring
  have halpha_lin : bernoulliPGcAlpha p = p * (2 * p - 1) := by
    unfold bernoulliPMismatch3CycleWeight at hcrit
    nlinarith [hcrit, hcube]
  unfold bernoulliPGcCriticalPolynomial
  nlinarith [hquad, halpha_lin]

/-- Bernoulli-`p` GC-defect far-field package: the concrete defect profile is odd, the positive
and negative far-field balances are the mismatch-three-cycle and Perron-root logarithmic mismatch,
and the zero-locus is exactly the golden-ratio critical bias.
    prop:fold-gauge-anomaly-bernoulli-p-gc-defect-farfield-critical -/
theorem paper_fold_gauge_anomaly_bernoulli_p_gc_defect_farfield_critical :
    (∀ p θ : ℝ, bernoulliPGcDefect p (-θ) = -bernoulliPGcDefect p θ) ∧
      (∀ p : ℝ,
        bernoulliPGcPositiveFarfieldBalance p =
          Real.log (bernoulliPMismatch3CycleWeight p / bernoulliPGcAlpha p ^ 3)) ∧
      (∀ p : ℝ,
        bernoulliPGcNegativeFarfieldBalance p = -bernoulliPGcPositiveFarfieldBalance p) ∧
      (∀ p : ℝ, 0 < p → p < 1 →
        (bernoulliPGcPositiveFarfieldBalance p = 0 ↔ p = (1 + Real.sqrt 5) / 4)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p θ
    unfold bernoulliPGcDefect
    rw [bernoulliPGcOddProfile_neg]
    ring
  · intro p
    rfl
  · intro p
    rfl
  · intro p hp hp'
    constructor
    · intro hbal
      exact (bernoulliPGcPoly_zero_iff_root hp hp').1 (bernoulliPGcPoly_zero_of_farfield_zero hp hp' hbal)
    · intro hp_eq
      exact bernoulliPGcFarfield_zero_of_poly_zero hp hp'
        ((bernoulliPGcPoly_zero_iff_root hp hp').2 hp_eq)

end Omega.Folding
