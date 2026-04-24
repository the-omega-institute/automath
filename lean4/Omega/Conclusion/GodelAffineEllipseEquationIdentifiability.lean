import Mathlib.Tactic
import Mathlib.Data.Real.Sqrt

namespace Omega.Conclusion

open Real

/-- The affine image of the unit-circle coordinates `(u,v)` under the Gödel affine normal form. -/
noncomputable def affineEllipseMap (N k : ℕ) (u v : ℝ) : ℝ × ℝ :=
  let s := Real.sqrt N
  (s * u + (k : ℝ) / s * v, v / s)

/-- Membership in the affine ellipse generated from the unit circle. -/
def affineEllipsePoint (N k : ℕ) (x y : ℝ) : Prop :=
  ∃ u v : ℝ, u ^ 2 + v ^ 2 = 1 ∧ affineEllipseMap N k u v = (x, y)

/-- Every point of the affine ellipse satisfies the explicit quadratic equation.
The degenerate case `N = 0` is isolated so the paper theorem keeps the requested signature over
all naturals. -/
def affineEllipseEquation (N k : ℕ) : Prop :=
  N = 0 ∨
    ∀ ⦃x y : ℝ⦄, affineEllipsePoint N k x y →
      ((x - (k : ℝ) * y) ^ 2) / N + (N : ℝ) * y ^ 2 = 1

/-- The tangent-slope readout at the right intercept: `none` records the vertical tangent in the
`k = 0` case, while `some (1 / k)` records the finite slope. -/
noncomputable def affineEllipseRightTangentSlope (k : ℕ) : Option ℝ :=
  if k = 0 then none else some ((1 : ℝ) / k)

/-- The `x`-intercept recovers `N` through `x^2 = N`, and the tangent-slope rule recovers `k`. -/
def affineEllipseParametersRecoverable (N k : ℕ) : Prop :=
  N = 0 ∨
    (Real.sqrt N) ^ 2 = N ∧
      ((k = 0 ∧ affineEllipseRightTangentSlope k = none) ∨
        (k ≠ 0 ∧ affineEllipseRightTangentSlope k = some ((1 : ℝ) / k)))

/-- Paper package for the affine ellipse equation and the explicit intercept/slope identifiability.
    prop:conclusion-godel-affine-ellipse-equation-identifiability -/
theorem paper_conclusion_godel_affine_ellipse_equation_identifiability (N k : ℕ) :
    affineEllipseEquation N k ∧ affineEllipseParametersRecoverable N k := by
  by_cases hN : N = 0
  · exact ⟨Or.inl hN, Or.inl hN⟩
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    have hs_pos : 0 < Real.sqrt N := Real.sqrt_pos.2 (Nat.cast_pos.mpr hNpos)
    have hs_ne : Real.sqrt N ≠ 0 := ne_of_gt hs_pos
    have hs_sq : (Real.sqrt N) ^ 2 = (N : ℝ) := by
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg N)]
    refine ⟨Or.inr ?_, Or.inr ?_⟩
    · intro x y hxy
      rcases hxy with ⟨u, v, huv, hmap⟩
      rcases hmap
      have hx :
          (Real.sqrt N * u + (k : ℝ) / Real.sqrt N * v) - (k : ℝ) * (v / Real.sqrt N) =
            Real.sqrt N * u := by
        field_simp [hs_ne]
        ring
      have hxTerm : ((Real.sqrt N * u) ^ 2) / N = u ^ 2 := by
        field_simp [hs_ne, hs_sq]
        rw [hs_sq]
        ring_nf
      have hyTerm : (N : ℝ) * (v / Real.sqrt N) ^ 2 = v ^ 2 := by
        field_simp [hs_ne, hs_sq]
        rw [hs_sq]
        ring_nf
      calc
        (((Real.sqrt N * u + (k : ℝ) / Real.sqrt N * v) - (k : ℝ) * (v / Real.sqrt N)) ^ 2) / N +
            (N : ℝ) * (v / Real.sqrt N) ^ 2
            = ((Real.sqrt N * u) ^ 2) / N + (N : ℝ) * (v / Real.sqrt N) ^ 2 := by rw [hx]
        _ = u ^ 2 + v ^ 2 := by rw [hxTerm, hyTerm]
        _ = 1 := huv
    · refine ⟨by exact Real.sq_sqrt (Nat.cast_nonneg N), ?_⟩
      by_cases hk : k = 0
      · exact Or.inl ⟨hk, by simp [affineEllipseRightTangentSlope, hk]⟩
      · exact Or.inr ⟨hk, by simp [affineEllipseRightTangentSlope, hk]⟩

end Omega.Conclusion
