import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyRateCurveIndexIdealFormula

namespace Omega.Folding

open Polynomial

/-- Chapter-local data for the singular-elimination linear eliminant `α u^4 = Φ(u)`. -/
structure FoldGaugeAnomalyRateCurveSingularEliminationData where
  phi : ℚ → ℚ

namespace FoldGaugeAnomalyRateCurveSingularEliminationData

/-- The eliminated projection polynomial on the `u`-line. -/
noncomputable def singularProjectionPolynomial
    (_D : FoldGaugeAnomalyRateCurveSingularEliminationData) : ℤ[X] :=
  gaugeAnomalyIndexIdeal

/-- The projection of the singular locus is the audited polynomial `u^5 D19(u)`. -/
def singularProjectionEqU5D19 (D : FoldGaugeAnomalyRateCurveSingularEliminationData) : Prop :=
  D.singularProjectionPolynomial = gaugeAnomalyUPowFiveD19

/-- The explicit zero-fiber factorization `R(α,0) = 10 α^2 (2 α - 1)^2`. -/
def zeroFiberPolynomial (α : ℚ) : ℚ :=
  10 * α ^ 2 * (2 * α - 1) ^ 2

/-- The singular points on the zero fiber are exactly `α = 0` and `α = 1/2`. -/
def zeroFiberClassified (_D : FoldGaugeAnomalyRateCurveSingularEliminationData) : Prop :=
  ∀ α : ℚ, zeroFiberPolynomial α = 0 ↔ α = 0 ∨ α = (1 / 2 : ℚ)

/-- The auxiliary linear eliminant `α u^4 = Φ(u)` determines at most one `α` over each nonzero
`u`, hence over each nonzero root of `D19`. -/
def d19FibersUnique (D : FoldGaugeAnomalyRateCurveSingularEliminationData) : Prop :=
  ∀ {u α β : ℚ}, u ≠ 0 → α * u ^ 4 = D.phi u → β * u ^ 4 = D.phi u → α = β

private theorem zeroFiberPolynomial_roots :
    ∀ α : ℚ, zeroFiberPolynomial α = 0 ↔ α = 0 ∨ α = (1 / 2 : ℚ) := by
  intro α
  constructor
  · intro hα
    have hprod : (10 : ℚ) * (α ^ 2 * (2 * α - 1) ^ 2) = 0 := by
      simpa [zeroFiberPolynomial, mul_assoc] using hα
    rcases mul_eq_zero.mp hprod with h10 | hrest
    · norm_num at h10
    · rcases mul_eq_zero.mp hrest with hsq | hlin
      · left
        nlinarith
      · right
        nlinarith
  · rintro (rfl | hhalf)
    · norm_num [zeroFiberPolynomial]
    · simpa [zeroFiberPolynomial, hhalf]

private theorem linearEliminant_unique (D : FoldGaugeAnomalyRateCurveSingularEliminationData) :
    D.d19FibersUnique := by
  intro u α β hu hα hβ
  have hu4 : u ^ 4 ≠ 0 := pow_ne_zero 4 hu
  apply mul_right_cancel₀ hu4
  calc
    α * u ^ 4 = D.phi u := hα
    _ = β * u ^ 4 := hβ.symm

/-- Paper label: `thm:fold-gauge-anomaly-rate-curve-singular-elimination-u5d19`.
The singular projection is the already-audited polynomial `u^5 D19(u)`, the zero fiber is exactly
the factorization `10 α^2 (2 α - 1)^2`, and the linear eliminant `α u^4 = Φ(u)` makes the
nonzero `D19` fibers unique. -/
theorem paper_fold_gauge_anomaly_rate_curve_singular_elimination_u5d19
    (D : FoldGaugeAnomalyRateCurveSingularEliminationData) :
    D.singularProjectionEqU5D19 ∧ D.zeroFiberClassified ∧ D.d19FibersUnique := by
  refine ⟨?_, zeroFiberPolynomial_roots, linearEliminant_unique D⟩
  simpa [singularProjectionEqU5D19, singularProjectionPolynomial] using
    paper_fold_gauge_anomaly_rate_curve_index_ideal_formula.2

end FoldGaugeAnomalyRateCurveSingularEliminationData

open FoldGaugeAnomalyRateCurveSingularEliminationData

theorem paper_fold_gauge_anomaly_rate_curve_singular_elimination_u5d19
    (D : FoldGaugeAnomalyRateCurveSingularEliminationData) :
    D.singularProjectionEqU5D19 ∧ D.zeroFiberClassified ∧ D.d19FibersUnique :=
  FoldGaugeAnomalyRateCurveSingularEliminationData.paper_fold_gauge_anomaly_rate_curve_singular_elimination_u5d19 D

end Omega.Folding
