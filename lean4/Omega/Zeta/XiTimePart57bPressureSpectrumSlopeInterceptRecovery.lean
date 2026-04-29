import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Zeta.XiTimePart57bPressureSpectrumDiscreteConvexityMonotoneExcess

open Filter Topology

namespace Omega.Zeta

/-- Concrete tail-freezing data for recovering the pressure-spectrum slope `α_*` and intercept
`g_*`. -/
structure xi_time_part57b_pressure_spectrum_slope_intercept_recovery_data where
  spectrum : XiTimePart57bPressureSpectrumDiscreteConvexityData
  freezingStart : ℕ
  frozen_tail :
    ∀ a : ℕ, freezingStart ≤ a →
      spectrum.P a = (a : ℝ) * spectrum.alphaStar + spectrum.gStar

namespace xi_time_part57b_pressure_spectrum_slope_intercept_recovery_data

/-- Recovery of the slope parameter from the high-order pressure spectrum. -/
def xi_time_part57b_pressure_spectrum_slope_intercept_recovery_slope_recovered
    (D : xi_time_part57b_pressure_spectrum_slope_intercept_recovery_data) : Prop :=
  Tendsto (fun a : ℕ => D.spectrum.P (a + 1) / ((a : ℝ) + 1)) atTop
    (nhds D.spectrum.alphaStar)

/-- Recovery of the frozen intercept from any pressure sample in the frozen tail. -/
def xi_time_part57b_pressure_spectrum_slope_intercept_recovery_intercept_recovered
    (D : xi_time_part57b_pressure_spectrum_slope_intercept_recovery_data) : Prop :=
  ∀ a : ℕ, D.freezingStart ≤ a →
    D.spectrum.gStar = D.spectrum.P a - (a : ℝ) * D.spectrum.alphaStar

end xi_time_part57b_pressure_spectrum_slope_intercept_recovery_data

open xi_time_part57b_pressure_spectrum_slope_intercept_recovery_data

/-- Paper label: `thm:xi-time-part57b-pressure-spectrum-slope-intercept-recovery`. The ground-state
sandwich bounds squeeze `P_a / a` to `α_*`, and the frozen-tail identity rewrites directly to
recover the intercept `g_*`. -/
theorem paper_xi_time_part57b_pressure_spectrum_slope_intercept_recovery
    (D : xi_time_part57b_pressure_spectrum_slope_intercept_recovery_data) :
    D.xi_time_part57b_pressure_spectrum_slope_intercept_recovery_slope_recovered ∧
      D.xi_time_part57b_pressure_spectrum_slope_intercept_recovery_intercept_recovered := by
  have hpackage := paper_xi_time_part57b_pressure_spectrum_discrete_convexity_monotone_excess D.spectrum
  have hLowerTail :
      Tendsto
        (fun a : ℕ =>
          D.spectrum.alphaStar + D.spectrum.gStar / ((a : ℝ) + 1))
        atTop (nhds D.spectrum.alphaStar) := by
    have htail :
        Tendsto (fun a : ℕ => D.spectrum.gStar / ((a : ℝ) + 1)) atTop (nhds 0) := by
      have hcomp :=
        (tendsto_const_div_atTop_nhds_zero_nat D.spectrum.gStar).comp (tendsto_add_atTop_nat 1)
      convert hcomp using 1 with a
      ext a
      simp [Function.comp, Nat.cast_add]
    simpa using tendsto_const_nhds.add htail
  have hUpperTail :
      Tendsto
        (fun a : ℕ =>
          D.spectrum.alphaStar + Real.log Real.goldenRatio / ((a : ℝ) + 1))
        atTop (nhds D.spectrum.alphaStar) := by
    have htail :
        Tendsto (fun a : ℕ => Real.log Real.goldenRatio / ((a : ℝ) + 1)) atTop (nhds 0) := by
      have hcomp :=
        (tendsto_const_div_atTop_nhds_zero_nat (Real.log Real.goldenRatio)).comp
          (tendsto_add_atTop_nat 1)
      convert hcomp using 1 with a
      ext a
      simp [Function.comp, Nat.cast_add]
    simpa using tendsto_const_nhds.add htail
  refine ⟨?_, ?_⟩
  · dsimp [xi_time_part57b_pressure_spectrum_slope_intercept_recovery_slope_recovered]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hLowerTail hUpperTail (fun a => ?_) (fun a => ?_)
    · have hlow := (hpackage.2.2 (a + 1)).1
      set n : ℝ := (a : ℝ) + 1
      have hpos : 0 < n := by
        dsimp [n]
        positivity
      have hcast : (((a + 1 : ℕ) : ℝ)) = n := by
        simp [n, Nat.cast_add]
      unfold XiTimePart57bPressureSpectrumDiscreteConvexityData.excess at hlow
      rw [hcast] at hlow
      have hmul : n * D.spectrum.alphaStar + D.spectrum.gStar ≤ D.spectrum.P (a + 1) := by
        nlinarith
      refine (le_div_iff₀ hpos).2 ?_
      have hne : n ≠ 0 := ne_of_gt hpos
      have hrewrite :
          (D.spectrum.alphaStar + D.spectrum.gStar / n) * n =
            n * D.spectrum.alphaStar + D.spectrum.gStar := by
        field_simp [hne]
      rw [hrewrite]
      exact hmul
    · have hupp := (hpackage.2.2 (a + 1)).2
      set n : ℝ := (a : ℝ) + 1
      have hpos : 0 < n := by
        dsimp [n]
        positivity
      have hcast : (((a + 1 : ℕ) : ℝ)) = n := by
        simp [n, Nat.cast_add]
      unfold XiTimePart57bPressureSpectrumDiscreteConvexityData.excess at hupp
      rw [hcast] at hupp
      have hmul : D.spectrum.P (a + 1) ≤ n * D.spectrum.alphaStar + Real.log Real.goldenRatio := by
        nlinarith
      refine (div_le_iff₀ hpos).2 ?_
      have hne : n ≠ 0 := ne_of_gt hpos
      have hrewrite :
          (D.spectrum.alphaStar + Real.log Real.goldenRatio / n) * n =
            n * D.spectrum.alphaStar + Real.log Real.goldenRatio := by
        field_simp [hne]
      rw [hrewrite]
      exact hmul
  · intro a ha
    rw [D.frozen_tail a ha]
    ring

end Omega.Zeta
