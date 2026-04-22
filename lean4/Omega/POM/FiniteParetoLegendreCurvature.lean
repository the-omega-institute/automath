import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- Concrete two-point finite Pareto/escort model used to package the Legendre geometry. The
support values are `0` and `1`, so the escort partition function is `w₀ + w₁ e^q`. -/
structure PomFiniteParetoLegendreData where
  leftWeight : ℝ
  rightWeight : ℝ
  leftWeight_pos : 0 < leftWeight
  rightWeight_pos : 0 < rightWeight

namespace PomFiniteParetoLegendreData

/-- Finite escort partition function `Z(q) = w₀ + w₁ e^q`. -/
def pom_finite_pareto_legendre_curvature_partition (D : PomFiniteParetoLegendreData) (q : ℝ) : ℝ :=
  D.leftWeight + D.rightWeight * Real.exp q

/-- Free energy `F(q) = log Z(q)`. -/
def pom_finite_pareto_legendre_curvature_freeEnergy (D : PomFiniteParetoLegendreData)
    (q : ℝ) : ℝ :=
  Real.log (D.pom_finite_pareto_legendre_curvature_partition q)

/-- Escort mean/slope `F'(q)`. -/
def pom_finite_pareto_legendre_curvature_slope (D : PomFiniteParetoLegendreData) (q : ℝ) : ℝ :=
  (D.rightWeight * Real.exp q) / D.pom_finite_pareto_legendre_curvature_partition q

/-- Escort variance `F''(q)`. -/
def pom_finite_pareto_legendre_curvature_variance (D : PomFiniteParetoLegendreData)
    (q : ℝ) : ℝ :=
  (D.leftWeight * D.rightWeight * Real.exp q) /
    (D.pom_finite_pareto_legendre_curvature_partition q) ^ 2

/-- Legendre-parametrized Pareto frontier point `(κ(q), H(q))`. -/
def pom_finite_pareto_legendre_curvature_legendrePoint (D : PomFiniteParetoLegendreData)
    (q : ℝ) : ℝ × ℝ :=
  (D.pom_finite_pareto_legendre_curvature_slope q,
    q * D.pom_finite_pareto_legendre_curvature_slope q -
      D.pom_finite_pareto_legendre_curvature_freeEnergy q)

/-- Curvature of the Legendre graph in the slope parameter: `d²H / dκ² = 1 / F''(q)`. -/
def pom_finite_pareto_legendre_curvature_legendreCurvature
    (D : PomFiniteParetoLegendreData) (q : ℝ) : ℝ :=
  (D.pom_finite_pareto_legendre_curvature_variance q)⁻¹

/-- Package of the derivative identities, strict slope monotonicity, and Legendre parametrization
for the concrete two-point finite Pareto model. -/
def strictLegendreGeometry (D : PomFiniteParetoLegendreData) : Prop :=
  (∀ q,
    HasDerivAt D.pom_finite_pareto_legendre_curvature_freeEnergy
      (D.pom_finite_pareto_legendre_curvature_slope q) q) ∧
    (∀ q,
      HasDerivAt D.pom_finite_pareto_legendre_curvature_slope
        (D.pom_finite_pareto_legendre_curvature_variance q) q) ∧
    (∀ q, 0 < D.pom_finite_pareto_legendre_curvature_variance q) ∧
    StrictMono D.pom_finite_pareto_legendre_curvature_slope ∧
    (∀ q,
      D.pom_finite_pareto_legendre_curvature_legendrePoint q =
        (D.pom_finite_pareto_legendre_curvature_slope q,
          q * D.pom_finite_pareto_legendre_curvature_slope q -
            D.pom_finite_pareto_legendre_curvature_freeEnergy q)) ∧
    (∀ q,
      D.pom_finite_pareto_legendre_curvature_legendreCurvature q =
        (D.pom_finite_pareto_legendre_curvature_variance q)⁻¹)

end PomFiniteParetoLegendreData

/-- Paper label: `thm:pom-finite-pareto-legendre-curvature`. In the explicit two-weight escort
model, `F(q) = log (w₀ + w₁ e^q)` has derivative equal to the escort mean, second derivative equal
to the escort variance, the slope map is strictly increasing, and the Pareto frontier is
parametrized by the Legendre transform with curvature `1 / F''(q)`. -/
theorem paper_pom_finite_pareto_legendre_curvature (D : PomFiniteParetoLegendreData) :
    D.strictLegendreGeometry := by
  have hpartition_pos :
      ∀ q, 0 < D.pom_finite_pareto_legendre_curvature_partition q := by
    intro q
    dsimp [PomFiniteParetoLegendreData.pom_finite_pareto_legendre_curvature_partition]
    have hexp_pos : 0 < Real.exp q := Real.exp_pos q
    nlinarith [D.leftWeight_pos, D.rightWeight_pos]
  have hnum :
      ∀ q, HasDerivAt (fun t => D.rightWeight * Real.exp t) (D.rightWeight * Real.exp q) q := by
    intro q
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Real.hasDerivAt_exp q).const_mul D.rightWeight
  have hpartition_deriv :
      ∀ q,
        HasDerivAt D.pom_finite_pareto_legendre_curvature_partition
          (D.rightWeight * Real.exp q) q := by
    intro q
    simpa [PomFiniteParetoLegendreData.pom_finite_pareto_legendre_curvature_partition,
      mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] using
      (hasDerivAt_const q D.leftWeight).add (hnum q)
  have hfree :
      ∀ q,
        HasDerivAt D.pom_finite_pareto_legendre_curvature_freeEnergy
          (D.pom_finite_pareto_legendre_curvature_slope q) q := by
    intro q
    simpa [PomFiniteParetoLegendreData.pom_finite_pareto_legendre_curvature_freeEnergy,
      PomFiniteParetoLegendreData.pom_finite_pareto_legendre_curvature_slope] using
      (hpartition_deriv q).log (ne_of_gt (hpartition_pos q))
  have hslope :
      ∀ q,
        HasDerivAt D.pom_finite_pareto_legendre_curvature_slope
          (D.pom_finite_pareto_legendre_curvature_variance q) q := by
    intro q
    have hquot :
        HasDerivAt D.pom_finite_pareto_legendre_curvature_slope
          (((D.rightWeight * Real.exp q) *
              D.pom_finite_pareto_legendre_curvature_partition q -
              (D.rightWeight * Real.exp q) * (D.rightWeight * Real.exp q)) /
            (D.pom_finite_pareto_legendre_curvature_partition q) ^ 2) q := by
      simpa [PomFiniteParetoLegendreData.pom_finite_pareto_legendre_curvature_slope] using
        (hnum q).div (hpartition_deriv q) (ne_of_gt (hpartition_pos q))
    convert hquot using 1
    unfold PomFiniteParetoLegendreData.pom_finite_pareto_legendre_curvature_variance
      PomFiniteParetoLegendreData.pom_finite_pareto_legendre_curvature_partition
    ring
  have hvariance_pos :
      ∀ q, 0 < D.pom_finite_pareto_legendre_curvature_variance q := by
    intro q
    have hpartition_sq_pos :
        0 < (D.pom_finite_pareto_legendre_curvature_partition q) ^ 2 := by
      exact sq_pos_of_pos (hpartition_pos q)
    have hnum_pos : 0 < D.leftWeight * D.rightWeight * Real.exp q := by
      have hexp_pos : 0 < Real.exp q := Real.exp_pos q
      exact mul_pos (mul_pos D.leftWeight_pos D.rightWeight_pos) hexp_pos
    dsimp [PomFiniteParetoLegendreData.pom_finite_pareto_legendre_curvature_variance]
    exact div_pos hnum_pos hpartition_sq_pos
  refine ⟨hfree, hslope, hvariance_pos, ?_, ?_, ?_⟩
  · exact strictMono_of_hasDerivAt_pos hslope hvariance_pos
  · intro q
    rfl
  · intro q
    rfl

end

end Omega.POM
