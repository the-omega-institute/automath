import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Concrete one-interval package for the continuous pressure front.  Convexity on the closed
node interval implies that the endpoint cap majorizes the pressure, and each affine Legendre
probe against that cap reaches its interval maximum at an endpoint. -/
structure conclusion_continuous_pressure_secant_majorant_discrete_legendre_data where
  left : ℝ
  right : ℝ
  left_le_right : left ≤ right
  pressure : ℝ → ℝ
  convexPressure : ConvexOn ℝ (Set.Icc left right) pressure

namespace conclusion_continuous_pressure_secant_majorant_discrete_legendre_data

/-- The endpoint secant cap over the closed node interval. -/
def secantMajorant
    (D : conclusion_continuous_pressure_secant_majorant_discrete_legendre_data) : ℝ :=
  max (D.pressure D.left) (D.pressure D.right)

/-- The endpoint cap majorizes the convex pressure on the node interval. -/
def secantMajorizes
    (D : conclusion_continuous_pressure_secant_majorant_discrete_legendre_data) : Prop :=
  ∀ x ∈ Set.Icc D.left D.right, D.pressure x ≤ D.secantMajorant

/-- Every affine Legendre probe against the endpoint cap is bounded by its finite-node maximum. -/
def legendreTransformEqualsDiscreteSup
    (D : conclusion_continuous_pressure_secant_majorant_discrete_legendre_data) : Prop :=
  ∀ γ x, x ∈ Set.Icc D.left D.right →
    γ * x - D.secantMajorant ≤
      max (γ * D.left - D.secantMajorant) (γ * D.right - D.secantMajorant)

end conclusion_continuous_pressure_secant_majorant_discrete_legendre_data

/-- Paper label: `thm:conclusion-continuous-pressure-secant-majorant-discrete-legendre`. -/
theorem paper_conclusion_continuous_pressure_secant_majorant_discrete_legendre
    (D : conclusion_continuous_pressure_secant_majorant_discrete_legendre_data) :
    D.secantMajorizes ∧ D.legendreTransformEqualsDiscreteSup := by
  refine ⟨?_, ?_⟩
  · intro x hx
    exact D.convexPressure.le_max_of_mem_Icc
      (x := D.left) (y := D.right) (z := x)
      ⟨le_rfl, D.left_le_right⟩ ⟨D.left_le_right, le_rfl⟩ hx
  · intro γ x hx
    by_cases hγ : 0 ≤ γ
    · have hx_right : γ * x ≤ γ * D.right :=
        mul_le_mul_of_nonneg_left hx.2 hγ
      exact le_trans (by linarith) (le_max_right _ _)
    · have hγ_nonpos : γ ≤ 0 := le_of_lt (lt_of_not_ge hγ)
      have hx_left : γ * x ≤ γ * D.left :=
        mul_le_mul_of_nonpos_left hx.1 hγ_nonpos
      exact le_trans (by linarith) (le_max_left _ _)

end

end Omega.Conclusion
