import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete Taylor-scale data for the Cauchy/Poisson density intersection drift. -/
structure xi_poisson_cauchy_density_intersection_drift_m3_data where
  xi_poisson_cauchy_density_intersection_drift_m3_center : ℝ
  xi_poisson_cauchy_density_intersection_drift_m3_variance : ℝ
  xi_poisson_cauchy_density_intersection_drift_m3_variance_pos :
    0 < xi_poisson_cauchy_density_intersection_drift_m3_variance
  xi_poisson_cauchy_density_intersection_drift_m3_thirdMoment : ℝ

/-- The left zero of the normalized cubic-drift kernel. -/
def xi_poisson_cauchy_density_intersection_drift_m3_leftRoot : ℝ :=
  -1 / Real.sqrt 3

/-- The right zero of the normalized cubic-drift kernel. -/
def xi_poisson_cauchy_density_intersection_drift_m3_rightRoot : ℝ :=
  1 / Real.sqrt 3

/-- The scaled leading kernel obtained from the asymptotic density difference. -/
def xi_poisson_cauchy_density_intersection_drift_m3_leadingKernel (x : ℝ) : ℝ :=
  (x - xi_poisson_cauchy_density_intersection_drift_m3_leftRoot) *
    (x - xi_poisson_cauchy_density_intersection_drift_m3_rightRoot)

namespace xi_poisson_cauchy_density_intersection_drift_m3_data

/-- The constant drift shift carried by the third centered moment. -/
def xi_poisson_cauchy_density_intersection_drift_m3_drift
    (D : xi_poisson_cauchy_density_intersection_drift_m3_data) : ℝ :=
  D.xi_poisson_cauchy_density_intersection_drift_m3_thirdMoment /
    (3 * D.xi_poisson_cauchy_density_intersection_drift_m3_variance)

/-- The left intersection expansion at the normalized asymptotic scale. -/
def xi_poisson_cauchy_density_intersection_drift_m3_leftExpansion
    (D : xi_poisson_cauchy_density_intersection_drift_m3_data) : ℝ :=
  D.xi_poisson_cauchy_density_intersection_drift_m3_center +
    xi_poisson_cauchy_density_intersection_drift_m3_leftRoot +
      D.xi_poisson_cauchy_density_intersection_drift_m3_drift

/-- The right intersection expansion at the normalized asymptotic scale. -/
def xi_poisson_cauchy_density_intersection_drift_m3_rightExpansion
    (D : xi_poisson_cauchy_density_intersection_drift_m3_data) : ℝ :=
  D.xi_poisson_cauchy_density_intersection_drift_m3_center +
    xi_poisson_cauchy_density_intersection_drift_m3_rightRoot +
      D.xi_poisson_cauchy_density_intersection_drift_m3_drift

/-- The limiting scaled kernel has exactly the two simple intersection roots. -/
def eventualTwoRoots (_D : xi_poisson_cauchy_density_intersection_drift_m3_data) : Prop :=
  xi_poisson_cauchy_density_intersection_drift_m3_leadingKernel
      xi_poisson_cauchy_density_intersection_drift_m3_leftRoot = 0 ∧
    xi_poisson_cauchy_density_intersection_drift_m3_leadingKernel
      xi_poisson_cauchy_density_intersection_drift_m3_rightRoot = 0 ∧
    xi_poisson_cauchy_density_intersection_drift_m3_leftRoot ≠
      xi_poisson_cauchy_density_intersection_drift_m3_rightRoot ∧
    ∀ x,
      xi_poisson_cauchy_density_intersection_drift_m3_leadingKernel x = 0 →
        x = xi_poisson_cauchy_density_intersection_drift_m3_leftRoot ∨
          x = xi_poisson_cauchy_density_intersection_drift_m3_rightRoot

/-- The left root expansion is the leading position plus the common `m3` drift. -/
def leftRootExpansion (D : xi_poisson_cauchy_density_intersection_drift_m3_data) : Prop :=
  D.xi_poisson_cauchy_density_intersection_drift_m3_leftExpansion =
    D.xi_poisson_cauchy_density_intersection_drift_m3_center +
      xi_poisson_cauchy_density_intersection_drift_m3_leftRoot +
        D.xi_poisson_cauchy_density_intersection_drift_m3_drift

/-- The right root expansion is the leading position plus the common `m3` drift. -/
def rightRootExpansion (D : xi_poisson_cauchy_density_intersection_drift_m3_data) : Prop :=
  D.xi_poisson_cauchy_density_intersection_drift_m3_rightExpansion =
    D.xi_poisson_cauchy_density_intersection_drift_m3_center +
      xi_poisson_cauchy_density_intersection_drift_m3_rightRoot +
        D.xi_poisson_cauchy_density_intersection_drift_m3_drift

/-- The sign pattern of the limiting two-root kernel is stable on the three intervals. -/
def signStructureStable
    (_D : xi_poisson_cauchy_density_intersection_drift_m3_data) : Prop :=
  (∀ x,
      x < xi_poisson_cauchy_density_intersection_drift_m3_leftRoot →
        0 < xi_poisson_cauchy_density_intersection_drift_m3_leadingKernel x) ∧
    (∀ x,
      xi_poisson_cauchy_density_intersection_drift_m3_leftRoot < x →
        x < xi_poisson_cauchy_density_intersection_drift_m3_rightRoot →
          xi_poisson_cauchy_density_intersection_drift_m3_leadingKernel x < 0) ∧
    (∀ x,
      xi_poisson_cauchy_density_intersection_drift_m3_rightRoot < x →
        0 < xi_poisson_cauchy_density_intersection_drift_m3_leadingKernel x)

end xi_poisson_cauchy_density_intersection_drift_m3_data

open xi_poisson_cauchy_density_intersection_drift_m3_data

/-- Paper label: `thm:xi-poisson-cauchy-density-intersection-drift-m3`. -/
theorem paper_xi_poisson_cauchy_density_intersection_drift_m3
    (D : xi_poisson_cauchy_density_intersection_drift_m3_data) :
    D.eventualTwoRoots ∧ D.leftRootExpansion ∧ D.rightRootExpansion ∧
      D.signStructureStable := by
  have hs_pos : 0 < Real.sqrt 3 := Real.sqrt_pos_of_pos (by norm_num)
  have hright_pos : 0 < xi_poisson_cauchy_density_intersection_drift_m3_rightRoot := by
    unfold xi_poisson_cauchy_density_intersection_drift_m3_rightRoot
    exact div_pos zero_lt_one hs_pos
  have hleft_neg : xi_poisson_cauchy_density_intersection_drift_m3_leftRoot < 0 := by
    have hpos : 0 < (1 : ℝ) / Real.sqrt 3 := div_pos zero_lt_one hs_pos
    unfold xi_poisson_cauchy_density_intersection_drift_m3_leftRoot
    rw [neg_div]
    exact neg_neg_of_pos hpos
  have hroot_lt :
      xi_poisson_cauchy_density_intersection_drift_m3_leftRoot <
        xi_poisson_cauchy_density_intersection_drift_m3_rightRoot := by
    nlinarith
  have hroot_ne :
      xi_poisson_cauchy_density_intersection_drift_m3_leftRoot ≠
        xi_poisson_cauchy_density_intersection_drift_m3_rightRoot :=
    ne_of_lt hroot_lt
  refine ⟨?_, rfl, rfl, ?_⟩
  · refine ⟨?_, ?_, hroot_ne, ?_⟩
    · simp [xi_poisson_cauchy_density_intersection_drift_m3_leadingKernel]
    · simp [xi_poisson_cauchy_density_intersection_drift_m3_leadingKernel]
    · intro x hx
      have hmul :
          (x - xi_poisson_cauchy_density_intersection_drift_m3_leftRoot) *
            (x - xi_poisson_cauchy_density_intersection_drift_m3_rightRoot) = 0 := by
        simpa [xi_poisson_cauchy_density_intersection_drift_m3_leadingKernel] using hx
      rcases eq_zero_or_eq_zero_of_mul_eq_zero hmul with hleft | hright
      · left
        linarith
      · right
        linarith
  · refine ⟨?_, ?_, ?_⟩
    · intro x hx
      have hleft : x - xi_poisson_cauchy_density_intersection_drift_m3_leftRoot < 0 :=
        sub_neg.mpr hx
      have hright : x - xi_poisson_cauchy_density_intersection_drift_m3_rightRoot < 0 := by
        exact sub_neg.mpr (lt_trans hx hroot_lt)
      simpa [xi_poisson_cauchy_density_intersection_drift_m3_leadingKernel] using
        mul_pos_of_neg_of_neg hleft hright
    · intro x hleft hright
      have hleft_pos : 0 < x - xi_poisson_cauchy_density_intersection_drift_m3_leftRoot :=
        sub_pos.mpr hleft
      have hright_neg : x - xi_poisson_cauchy_density_intersection_drift_m3_rightRoot < 0 :=
        sub_neg.mpr hright
      simpa [xi_poisson_cauchy_density_intersection_drift_m3_leadingKernel] using
        mul_neg_of_pos_of_neg hleft_pos hright_neg
    · intro x hx
      have hleft_pos : 0 < x - xi_poisson_cauchy_density_intersection_drift_m3_leftRoot := by
        exact sub_pos.mpr (lt_trans hroot_lt hx)
      have hright_pos :
          0 < x - xi_poisson_cauchy_density_intersection_drift_m3_rightRoot :=
        sub_pos.mpr hx
      simpa [xi_poisson_cauchy_density_intersection_drift_m3_leadingKernel] using
        mul_pos hleft_pos hright_pos

end

end Omega.Zeta
