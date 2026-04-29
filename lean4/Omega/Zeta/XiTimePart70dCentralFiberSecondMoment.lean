import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.Zeta

noncomputable section

/-- The reciprocal golden ratio used in the central-fiber moment constants. -/
def xi_time_part70d_central_fiber_second_moment_phiInv : ℝ :=
  Real.goldenRatio⁻¹

/-- Concrete moment-limit data for the central-fiber field. -/
structure xi_time_part70d_central_fiber_second_moment_data where
  xi_time_part70d_central_fiber_second_moment_firstMoment : ℕ → ℝ
  xi_time_part70d_central_fiber_second_moment_secondMoment : ℕ → ℝ
  xi_time_part70d_central_fiber_second_moment_first_limit :
    Tendsto xi_time_part70d_central_fiber_second_moment_firstMoment atTop
      (nhds
        (xi_time_part70d_central_fiber_second_moment_phiInv +
          xi_time_part70d_central_fiber_second_moment_phiInv ^ 3))
  xi_time_part70d_central_fiber_second_moment_second_limit :
    Tendsto xi_time_part70d_central_fiber_second_moment_secondMoment atTop
      (nhds
        (xi_time_part70d_central_fiber_second_moment_phiInv +
          xi_time_part70d_central_fiber_second_moment_phiInv ^ 4))

/-- Scaled variance, expressed as the second scaled moment minus the square of the first. -/
def xi_time_part70d_central_fiber_second_moment_variance
    (D : xi_time_part70d_central_fiber_second_moment_data) (m : ℕ) : ℝ :=
  D.xi_time_part70d_central_fiber_second_moment_secondMoment m -
    D.xi_time_part70d_central_fiber_second_moment_firstMoment m ^ 2

/-- The paper-facing second-moment and variance limits. -/
def xi_time_part70d_central_fiber_second_moment_statement
    (D : xi_time_part70d_central_fiber_second_moment_data) : Prop :=
  Tendsto D.xi_time_part70d_central_fiber_second_moment_secondMoment atTop
      (nhds (2 * xi_time_part70d_central_fiber_second_moment_phiInv ^ 2)) ∧
    Tendsto (xi_time_part70d_central_fiber_second_moment_variance D) atTop
      (nhds (xi_time_part70d_central_fiber_second_moment_phiInv ^ 7))

lemma xi_time_part70d_central_fiber_second_moment_phiInv_sq :
    xi_time_part70d_central_fiber_second_moment_phiInv ^ 2 =
      1 - xi_time_part70d_central_fiber_second_moment_phiInv := by
  have hinv_conj : (Real.goldenRatio⁻¹ : ℝ) = -Real.goldenConj := by
    simpa [one_div] using Real.inv_goldenRatio
  have hinv : (Real.goldenRatio⁻¹ : ℝ) = Real.goldenRatio - 1 := by
    nlinarith [hinv_conj, Real.goldenRatio_add_goldenConj]
  rw [xi_time_part70d_central_fiber_second_moment_phiInv]
  nlinarith [Real.goldenRatio_sq, hinv]

lemma xi_time_part70d_central_fiber_second_moment_second_constant :
    xi_time_part70d_central_fiber_second_moment_phiInv +
        xi_time_part70d_central_fiber_second_moment_phiInv ^ 4 =
      2 * xi_time_part70d_central_fiber_second_moment_phiInv ^ 2 := by
  have hsq := xi_time_part70d_central_fiber_second_moment_phiInv_sq
  nlinarith

lemma xi_time_part70d_central_fiber_second_moment_variance_constant :
    2 * xi_time_part70d_central_fiber_second_moment_phiInv ^ 2 -
        (xi_time_part70d_central_fiber_second_moment_phiInv +
          xi_time_part70d_central_fiber_second_moment_phiInv ^ 3) ^ 2 =
      xi_time_part70d_central_fiber_second_moment_phiInv ^ 7 := by
  have hsq := xi_time_part70d_central_fiber_second_moment_phiInv_sq
  have hcube :
      xi_time_part70d_central_fiber_second_moment_phiInv ^ 3 =
        2 * xi_time_part70d_central_fiber_second_moment_phiInv - 1 := by
    calc
      xi_time_part70d_central_fiber_second_moment_phiInv ^ 3 =
          xi_time_part70d_central_fiber_second_moment_phiInv *
            xi_time_part70d_central_fiber_second_moment_phiInv ^ 2 := by ring
      _ = xi_time_part70d_central_fiber_second_moment_phiInv *
          (1 - xi_time_part70d_central_fiber_second_moment_phiInv) := by rw [hsq]
      _ = 2 * xi_time_part70d_central_fiber_second_moment_phiInv - 1 := by
        nlinarith [hsq]
  have hfour :
      xi_time_part70d_central_fiber_second_moment_phiInv ^ 4 =
        2 - 3 * xi_time_part70d_central_fiber_second_moment_phiInv := by
    calc
      xi_time_part70d_central_fiber_second_moment_phiInv ^ 4 =
          (xi_time_part70d_central_fiber_second_moment_phiInv ^ 2) ^ 2 := by ring
      _ = (1 - xi_time_part70d_central_fiber_second_moment_phiInv) ^ 2 := by rw [hsq]
      _ = 2 - 3 * xi_time_part70d_central_fiber_second_moment_phiInv := by
        nlinarith [hsq]
  have hfive :
      xi_time_part70d_central_fiber_second_moment_phiInv ^ 5 =
        5 * xi_time_part70d_central_fiber_second_moment_phiInv - 3 := by
    calc
      xi_time_part70d_central_fiber_second_moment_phiInv ^ 5 =
          xi_time_part70d_central_fiber_second_moment_phiInv *
            xi_time_part70d_central_fiber_second_moment_phiInv ^ 4 := by ring
      _ = xi_time_part70d_central_fiber_second_moment_phiInv *
          (2 - 3 * xi_time_part70d_central_fiber_second_moment_phiInv) := by rw [hfour]
      _ = 5 * xi_time_part70d_central_fiber_second_moment_phiInv - 3 := by
        nlinarith [hsq]
  have hsix :
      xi_time_part70d_central_fiber_second_moment_phiInv ^ 6 =
        5 - 8 * xi_time_part70d_central_fiber_second_moment_phiInv := by
    calc
      xi_time_part70d_central_fiber_second_moment_phiInv ^ 6 =
          xi_time_part70d_central_fiber_second_moment_phiInv *
            xi_time_part70d_central_fiber_second_moment_phiInv ^ 5 := by ring
      _ = xi_time_part70d_central_fiber_second_moment_phiInv *
          (5 * xi_time_part70d_central_fiber_second_moment_phiInv - 3) := by rw [hfive]
      _ = 5 - 8 * xi_time_part70d_central_fiber_second_moment_phiInv := by
        nlinarith [hsq]
  have hseven :
      xi_time_part70d_central_fiber_second_moment_phiInv ^ 7 =
        13 * xi_time_part70d_central_fiber_second_moment_phiInv - 8 := by
    calc
      xi_time_part70d_central_fiber_second_moment_phiInv ^ 7 =
          xi_time_part70d_central_fiber_second_moment_phiInv *
            xi_time_part70d_central_fiber_second_moment_phiInv ^ 6 := by ring
      _ = xi_time_part70d_central_fiber_second_moment_phiInv *
          (5 - 8 * xi_time_part70d_central_fiber_second_moment_phiInv) := by rw [hsix]
      _ = 13 * xi_time_part70d_central_fiber_second_moment_phiInv - 8 := by
        nlinarith [hsq]
  nlinarith [hsq, hcube, hseven]

/-- Paper label: `thm:xi-time-part70d-central-fiber-second-moment`. -/
theorem paper_xi_time_part70d_central_fiber_second_moment
    (D : xi_time_part70d_central_fiber_second_moment_data) :
    xi_time_part70d_central_fiber_second_moment_statement D := by
  constructor
  · simpa [xi_time_part70d_central_fiber_second_moment_second_constant] using
      D.xi_time_part70d_central_fiber_second_moment_second_limit
  · have hfirst_sq :
        Tendsto
          (fun m : ℕ =>
            D.xi_time_part70d_central_fiber_second_moment_firstMoment m ^ 2) atTop
          (nhds
            ((xi_time_part70d_central_fiber_second_moment_phiInv +
                xi_time_part70d_central_fiber_second_moment_phiInv ^ 3) ^ 2)) :=
      D.xi_time_part70d_central_fiber_second_moment_first_limit.pow 2
    have hvar :
        Tendsto (xi_time_part70d_central_fiber_second_moment_variance D) atTop
          (nhds
            ((xi_time_part70d_central_fiber_second_moment_phiInv +
                xi_time_part70d_central_fiber_second_moment_phiInv ^ 4) -
              (xi_time_part70d_central_fiber_second_moment_phiInv +
                xi_time_part70d_central_fiber_second_moment_phiInv ^ 3) ^ 2)) := by
      simpa [xi_time_part70d_central_fiber_second_moment_variance] using
        D.xi_time_part70d_central_fiber_second_moment_second_limit.sub hfirst_sq
    simpa [xi_time_part70d_central_fiber_second_moment_second_constant,
      xi_time_part70d_central_fiber_second_moment_variance_constant] using hvar

end

end Omega.Zeta
