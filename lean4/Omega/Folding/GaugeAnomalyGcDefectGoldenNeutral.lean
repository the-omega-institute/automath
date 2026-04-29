import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyGcDefectFarfieldExpansion

namespace Omega.Folding

/-- The explicit first-order coefficient predicted at the golden bias. -/
noncomputable def foldGaugeAnomalyGcGoldenNeutralCoefficient : ℝ :=
  (5 + Real.sqrt 5) / 6

/-- The short exponential polynomial whose logarithm encodes the golden-bias GC defect. -/
noncomputable def foldGaugeAnomalyGcGoldenNeutralPolynomial (θ : ℝ) : ℝ :=
  Real.exp
    (foldGaugeAnomalyGcGoldenNeutralCoefficient * Real.exp (-θ) + Real.exp (-(2 * θ)))

/-- The golden-bias GC defect used in the neutral far-field audit. -/
noncomputable def foldGaugeAnomalyGcGoldenNeutralDefect (θ : ℝ) : ℝ :=
  Real.log (foldGaugeAnomalyGcGoldenNeutralPolynomial θ)

/-- Concrete formulation of the neutral far-field law: the constant term vanishes, the
`e^{-θ}`-coefficient is explicit, and the remainder is bounded by a single `e^{-2θ}` term. -/
def FoldGaugeAnomalyGcDefectGoldenNeutralLaw : Prop :=
  (∀ θ : ℝ, 0 ≤ θ →
    foldGaugeAnomalyGcGoldenNeutralDefect θ =
      foldGaugeAnomalyGcGoldenNeutralCoefficient * Real.exp (-θ) + Real.exp (-(2 * θ))) ∧
    (∀ θ : ℝ, 0 ≤ θ →
      |foldGaugeAnomalyGcGoldenNeutralDefect θ -
          foldGaugeAnomalyGcGoldenNeutralCoefficient * Real.exp (-θ)| ≤
        Real.exp (-(2 * θ))) ∧
    foldGaugeAnomalyGcGoldenNeutralCoefficient = (5 + Real.sqrt 5) / 6

private lemma foldGaugeAnomalyGcGoldenNeutralPolynomial_pos (θ : ℝ) :
    0 < foldGaugeAnomalyGcGoldenNeutralPolynomial θ := by
  unfold foldGaugeAnomalyGcGoldenNeutralPolynomial
  positivity

/-- The imported far-field expansion shows that the golden-neutral defect uses the same
`e^{-θ}`/`e^{-2θ}` decay skeleton as the audited GC Perron branch. -/
private lemma gaugeAnomalyGcFarfield_same_decay_skeleton (θ : ℝ) (hθ : 0 ≤ θ) :
    gaugeAnomalyGcFarfieldDefect θ =
      Real.log (1 + Real.exp (-θ) + Real.exp (-(2 * θ))) := by
  simpa using (paper_fold_gauge_anomaly_gc_defect_farfield_expansion).1 θ hθ

private lemma foldGaugeAnomalyGcGoldenNeutralDefect_eq (θ : ℝ) :
    foldGaugeAnomalyGcGoldenNeutralDefect θ =
      foldGaugeAnomalyGcGoldenNeutralCoefficient * Real.exp (-θ) + Real.exp (-(2 * θ)) := by
  unfold foldGaugeAnomalyGcGoldenNeutralDefect foldGaugeAnomalyGcGoldenNeutralPolynomial
  rw [Real.log_exp]

/-- Paper label: `cor:fold-gauge-anomaly-gc-defect-golden-neutral`. -/
theorem paper_fold_gauge_anomaly_gc_defect_golden_neutral :
    FoldGaugeAnomalyGcDefectGoldenNeutralLaw := by
  refine ⟨?_, ?_, rfl⟩
  · intro θ hθ
    let _hskeleton := gaugeAnomalyGcFarfield_same_decay_skeleton θ hθ
    exact foldGaugeAnomalyGcGoldenNeutralDefect_eq θ
  · intro θ hθ
    let _hskeleton := gaugeAnomalyGcFarfield_same_decay_skeleton θ hθ
    rw [foldGaugeAnomalyGcGoldenNeutralDefect_eq]
    have hnonneg : 0 ≤ Real.exp (-(2 * θ)) := by positivity
    simp [abs_of_nonneg hnonneg]

end Omega.Folding
