import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyTrigonalDiscUFactorization

namespace Omega.Folding

noncomputable section

/-- Concrete seed data for the first trigonal branch-parameter audit. -/
structure FirstTrigonalStructureGoldenRatioData where
  mu : ℚ

namespace FirstTrigonalStructureGoldenRatioData

/-- The cubic obtained by substituting the distinguished line through the golden-ratio branch
point. -/
def trigonalCubic (u : ℝ) : ℝ :=
  u ^ 3 - 3 * Real.goldenRatio * u ^ 2 + 3 * Real.goldenRatio ^ 2 * u - Real.goldenRatio ^ 3

/-- The unfactored discriminant from the trigonal audit. -/
def trigonalDiscriminant (μ : ℚ) : ℚ :=
  -μ * (32 * (μ ^ 2 - μ - 1) + 27 * μ ^ 5) * (μ ^ 2 - μ - 1) ^ 2

/-- The factored discriminant separating the branch-parameter components. -/
def factoredTrigonalDiscriminant (μ : ℚ) : ℚ :=
  -μ * (3 * μ + 2) * (μ ^ 2 - μ - 1) ^ 2 * (9 * μ ^ 4 - 6 * μ ^ 3 + 4 * μ ^ 2 + 8 * μ - 16)

/-- The golden-ratio specialization is the pure cube `(u - φ)^3`. -/
def cubicModel (_D : FirstTrigonalStructureGoldenRatioData) : Prop :=
  ∀ u : ℝ, trigonalCubic u = (u - Real.goldenRatio) ^ 3

/-- The trigonal discriminant factors exactly as in the audited branch computation. -/
def discriminantFactorization (D : FirstTrigonalStructureGoldenRatioData) : Prop :=
  trigonalDiscriminant D.mu = factoredTrigonalDiscriminant D.mu

/-- Every branch parameter lies on one of the explicit discriminant factors. -/
def branchParameterDescription (D : FirstTrigonalStructureGoldenRatioData) : Prop :=
  trigonalDiscriminant D.mu = 0 →
    D.mu = 0 ∨ 3 * D.mu + 2 = 0 ∨ D.mu ^ 2 - D.mu - 1 = 0 ∨
      9 * D.mu ^ 4 - 6 * D.mu ^ 3 + 4 * D.mu ^ 2 + 8 * D.mu - 16 = 0

/-- The golden-ratio specialization produces a triple ramification point. -/
def goldenRatioTripleRamification (D : FirstTrigonalStructureGoldenRatioData) : Prop :=
  D.cubicModel ∧ trigonalCubic Real.goldenRatio = 0

lemma cubicModel_true (D : FirstTrigonalStructureGoldenRatioData) : D.cubicModel := by
  intro u
  dsimp [cubicModel, trigonalCubic]
  ring

lemma discriminantFactorization_true (D : FirstTrigonalStructureGoldenRatioData) :
    D.discriminantFactorization := by
  simpa [discriminantFactorization, trigonalDiscriminant, factoredTrigonalDiscriminant] using
    paper_fold_gauge_anomaly_trigonal_disc_u_factorization D.mu

lemma branchParameterDescription_true (D : FirstTrigonalStructureGoldenRatioData) :
    D.branchParameterDescription := by
  intro hdisc
  have hfactor : factoredTrigonalDiscriminant D.mu = 0 := by
    rw [← D.discriminantFactorization_true]
    exact hdisc
  dsimp [factoredTrigonalDiscriminant] at hfactor
  rcases mul_eq_zero.mp hfactor with hleft | hquartic
  · rcases mul_eq_zero.mp hleft with hleft' | hsquare
    · rcases mul_eq_zero.mp hleft' with hmu | hlinear
      · left
        linarith
      · right
        left
        linarith
    · right
      right
      left
      exact eq_zero_of_pow_eq_zero hsquare
  · right
    right
    right
    exact hquartic

lemma goldenRatioTripleRamification_true (D : FirstTrigonalStructureGoldenRatioData) :
    D.goldenRatioTripleRamification := by
  refine ⟨D.cubicModel_true, ?_⟩
  simpa using D.cubicModel_true Real.goldenRatio

end FirstTrigonalStructureGoldenRatioData

open FirstTrigonalStructureGoldenRatioData

/-- Paper label: `thm:fold-gauge-anomaly-first-trigonal-structure-golden-ratio`. The golden-ratio
line specialization collapses to a cube, the discriminant factorization isolates the branch
locus, and the golden-ratio branch yields triple ramification. -/
theorem paper_fold_gauge_anomaly_first_trigonal_structure_golden_ratio
    (D : FirstTrigonalStructureGoldenRatioData) :
    D.cubicModel ∧ D.discriminantFactorization ∧ D.branchParameterDescription ∧
      D.goldenRatioTripleRamification := by
  exact ⟨D.cubicModel_true, D.discriminantFactorization_true, D.branchParameterDescription_true,
    D.goldenRatioTripleRamification_true⟩

end

end Omega.Folding
