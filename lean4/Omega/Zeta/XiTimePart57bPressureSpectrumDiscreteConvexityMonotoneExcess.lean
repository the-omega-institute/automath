import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic
import Omega.Folding.FoldPressureGroundstateBounds

open Filter Topology

namespace Omega.Zeta

open Omega.Folding

/-- Concrete asymptotic data for the integer pressure spectrum `P_a` coming from the finite-volume
power sums `S_a(m)`, the maximal fiber scale `M_m`, and the lower/upper ground-state comparison
terms. -/
structure XiTimePart57bPressureSpectrumDiscreteConvexityData where
  S : ℕ → ℕ → ℝ
  M : ℕ → ℝ
  K : ℕ → ℝ
  X : ℕ → ℝ
  P : ℕ → ℝ
  alphaStar : ℝ
  gStar : ℝ
  hS_pos : ∀ a m, 0 < S a (m + 1)
  hM_pos : ∀ m, 0 < M (m + 1)
  hK_pos : ∀ m, 0 < K (m + 1)
  hX_pos : ∀ m, 0 < X (m + 1)
  h_logconvex : ∀ a m, S (a + 1) (m + 1) ^ 2 ≤ S a (m + 1) * S (a + 2) (m + 1)
  h_maxBound : ∀ a m, S (a + 1) (m + 1) ≤ M (m + 1) * S a (m + 1)
  h_lowerDom : ∀ a m, K (m + 1) * M (m + 1) ^ a ≤ S a (m + 1)
  h_upperDom : ∀ a m, S a (m + 1) ≤ X (m + 1) * M (m + 1) ^ a
  hP : ∀ a, Tendsto (foldPressureSeq S a) atTop (nhds (P a))
  hAlpha :
    Tendsto (fun m : ℕ => (1 / (((m + 1 : ℕ) : ℝ))) * Real.log (M (m + 1))) atTop
      (nhds alphaStar)
  hLower :
    ∀ a,
      Tendsto (foldGroundstateLowerSeq K M a) atTop
        (nhds (foldGroundstateLowerBound a alphaStar gStar))
  hUpper :
    ∀ a,
      Tendsto (foldGroundstateUpperSeq X M a) atTop
        (nhds (foldGroundstateUpperBound a alphaStar))

namespace XiTimePart57bPressureSpectrumDiscreteConvexityData

/-- Ground-state excess `E_a = P_a - a α_*`. -/
def excess (D : XiTimePart57bPressureSpectrumDiscreteConvexityData) (a : ℕ) : ℝ :=
  D.P a - (a : ℝ) * D.alphaStar

/-- Discrete convexity of the pressure spectrum. -/
def discreteConvexity (D : XiTimePart57bPressureSpectrumDiscreteConvexityData) : Prop :=
  ∀ a : ℕ, 2 * D.P (a + 1) ≤ D.P a + D.P (a + 2)

/-- Monotonic decay of the ground-state excess. -/
def excessMonotone (D : XiTimePart57bPressureSpectrumDiscreteConvexityData) : Prop :=
  ∀ a : ℕ, D.excess (a + 1) ≤ D.excess a

/-- The ground-state sandwich `g_* ≤ E_a ≤ log φ`. -/
def excessBounds (D : XiTimePart57bPressureSpectrumDiscreteConvexityData) : Prop :=
  ∀ a : ℕ, D.gStar ≤ D.excess a ∧ D.excess a ≤ Real.log Real.goldenRatio

end XiTimePart57bPressureSpectrumDiscreteConvexityData

private lemma
    xi_time_part57b_pressure_spectrum_discrete_convexity_monotone_excess_logconvex_pointwise
    (D : XiTimePart57bPressureSpectrumDiscreteConvexityData) (a m : ℕ) :
    2 * foldPressureSeq D.S (a + 1) m ≤ foldPressureSeq D.S a m + foldPressureSeq D.S (a + 2) m := by
  have hs0 : 0 < D.S a (m + 1) := D.hS_pos a m
  have hs1 : 0 < D.S (a + 1) (m + 1) := D.hS_pos (a + 1) m
  have hs2 : 0 < D.S (a + 2) (m + 1) := D.hS_pos (a + 2) m
  have hlog :
      2 * Real.log (D.S (a + 1) (m + 1)) ≤
        Real.log (D.S a (m + 1)) + Real.log (D.S (a + 2) (m + 1)) := by
    have hmul :
        D.S (a + 1) (m + 1) * D.S (a + 1) (m + 1) ≤ D.S a (m + 1) * D.S (a + 2) (m + 1) := by
      simpa [pow_two] using D.h_logconvex a m
    calc
      2 * Real.log (D.S (a + 1) (m + 1))
          = Real.log (D.S (a + 1) (m + 1) * D.S (a + 1) (m + 1)) := by
              rw [Real.log_mul hs1.ne' hs1.ne']
              ring
      _ ≤ Real.log (D.S a (m + 1) * D.S (a + 2) (m + 1)) := by
          exact Real.log_le_log (mul_pos hs1 hs1) hmul
      _ = Real.log (D.S a (m + 1)) + Real.log (D.S (a + 2) (m + 1)) := by
          rw [Real.log_mul hs0.ne' hs2.ne']
  have hfac : 0 ≤ 1 / (((m + 1 : ℕ) : ℝ)) := by positivity
  unfold foldPressureSeq
  nlinarith [mul_le_mul_of_nonneg_left hlog hfac]

private lemma
    xi_time_part57b_pressure_spectrum_discrete_convexity_monotone_excess_max_bound_pointwise
    (D : XiTimePart57bPressureSpectrumDiscreteConvexityData) (a m : ℕ) :
    foldPressureSeq D.S (a + 1) m -
        ((a + 1 : ℕ) : ℝ) * ((1 / (((m + 1 : ℕ) : ℝ))) * Real.log (D.M (m + 1))) ≤
      foldPressureSeq D.S a m - (a : ℝ) * ((1 / (((m + 1 : ℕ) : ℝ))) * Real.log (D.M (m + 1))) := by
  have hs0 : 0 < D.S a (m + 1) := D.hS_pos a m
  have hs1 : 0 < D.S (a + 1) (m + 1) := D.hS_pos (a + 1) m
  have hm : 0 < D.M (m + 1) := D.hM_pos m
  set c : ℝ := 1 / (((m + 1 : ℕ) : ℝ))
  set u : ℝ := c * Real.log (D.M (m + 1))
  have hlog :
      Real.log (D.S (a + 1) (m + 1)) ≤
        Real.log (D.M (m + 1)) + Real.log (D.S a (m + 1)) := by
    calc
      Real.log (D.S (a + 1) (m + 1)) ≤ Real.log (D.M (m + 1) * D.S a (m + 1)) := by
          exact Real.log_le_log hs1 (D.h_maxBound a m)
      _ = Real.log (D.M (m + 1)) + Real.log (D.S a (m + 1)) := by
          rw [Real.log_mul hm.ne' hs0.ne']
  have hfac : 0 ≤ c := by
    dsimp [c]
    positivity
  have hscaled :
      c * Real.log (D.S (a + 1) (m + 1)) ≤ u + c * Real.log (D.S a (m + 1)) := by
    have := mul_le_mul_of_nonneg_left hlog hfac
    simpa [u, left_distrib, mul_add, add_comm, add_left_comm, add_assoc] using this
  have hstep :
      c * Real.log (D.S (a + 1) (m + 1)) - (((a + 1 : ℕ) : ℝ) * u) ≤
        (u + c * Real.log (D.S a (m + 1))) - (((a + 1 : ℕ) : ℝ) * u) := by
    exact sub_le_sub_right hscaled (((a + 1 : ℕ) : ℝ) * u)
  have hcast :
      (((a + 1 : ℕ) : ℝ) * u) = (a : ℝ) * u + u := by
    rw [Nat.cast_add, Nat.cast_one]
    ring
  unfold foldPressureSeq
  change
    c * Real.log (D.S (a + 1) (m + 1)) - (((a + 1 : ℕ) : ℝ) * u) ≤
      c * Real.log (D.S a (m + 1)) - (a : ℝ) * u
  calc
    c * Real.log (D.S (a + 1) (m + 1)) - (((a + 1 : ℕ) : ℝ) * u)
        ≤ (u + c * Real.log (D.S a (m + 1))) - (((a + 1 : ℕ) : ℝ) * u) := hstep
    _ = c * Real.log (D.S a (m + 1)) - (a : ℝ) * u := by
      rw [hcast]
      ring

private lemma
    xi_time_part57b_pressure_spectrum_discrete_convexity_monotone_excess_discrete_convexity
    (D : XiTimePart57bPressureSpectrumDiscreteConvexityData) :
    D.discreteConvexity := by
  intro a
  have hleft :
      Tendsto (fun m : ℕ => 2 * foldPressureSeq D.S (a + 1) m) atTop
        (nhds (2 * D.P (a + 1))) := by
    simpa using (D.hP (a + 1)).const_mul 2
  have hright :
      Tendsto (fun m : ℕ => foldPressureSeq D.S a m + foldPressureSeq D.S (a + 2) m) atTop
        (nhds (D.P a + D.P (a + 2))) :=
    (D.hP a).add (D.hP (a + 2))
  exact le_of_tendsto_of_tendsto' hleft hright
    (fun m => xi_time_part57b_pressure_spectrum_discrete_convexity_monotone_excess_logconvex_pointwise
      D a m)

private lemma
    xi_time_part57b_pressure_spectrum_discrete_convexity_monotone_excess_excess_monotone
    (D : XiTimePart57bPressureSpectrumDiscreteConvexityData) :
    D.excessMonotone := by
  intro a
  have hrate_succ :
      Tendsto
        (fun m : ℕ =>
          ((a + 1 : ℕ) : ℝ) * ((1 / (((m + 1 : ℕ) : ℝ))) * Real.log (D.M (m + 1)))
        )
        atTop
        (nhds (((a + 1 : ℕ) : ℝ) * D.alphaStar)) := by
    simpa using D.hAlpha.const_mul (((a + 1 : ℕ) : ℝ))
  have hrate :
      Tendsto
        (fun m : ℕ => (a : ℝ) * ((1 / (((m + 1 : ℕ) : ℝ))) * Real.log (D.M (m + 1)))
        )
        atTop
        (nhds ((a : ℝ) * D.alphaStar)) := by
    simpa using D.hAlpha.const_mul (a : ℝ)
  have hleft :
      Tendsto
        (fun m : ℕ =>
          foldPressureSeq D.S (a + 1) m -
            ((a + 1 : ℕ) : ℝ) * ((1 / (((m + 1 : ℕ) : ℝ))) * Real.log (D.M (m + 1)))
        )
        atTop
        (nhds (D.excess (a + 1))) := by
    simpa [XiTimePart57bPressureSpectrumDiscreteConvexityData.excess] using (D.hP (a + 1)).sub hrate_succ
  have hright :
      Tendsto
        (fun m : ℕ =>
          foldPressureSeq D.S a m -
            (a : ℝ) * ((1 / (((m + 1 : ℕ) : ℝ))) * Real.log (D.M (m + 1)))
        )
        atTop
        (nhds (D.excess a)) := by
    simpa [XiTimePart57bPressureSpectrumDiscreteConvexityData.excess] using (D.hP a).sub hrate
  exact le_of_tendsto_of_tendsto' hleft hright
    (fun m =>
      xi_time_part57b_pressure_spectrum_discrete_convexity_monotone_excess_max_bound_pointwise
        D a m)

private lemma
    xi_time_part57b_pressure_spectrum_discrete_convexity_monotone_excess_excess_bounds
    (D : XiTimePart57bPressureSpectrumDiscreteConvexityData) :
    D.excessBounds := by
  intro a
  rcases
      paper_fold_pressure_groundstate_bounds D.S D.M D.K D.X D.P D.alphaStar D.gStar
        D.h_lowerDom D.h_upperDom D.hK_pos D.hM_pos D.hX_pos D.hS_pos D.hP D.hLower D.hUpper a with
    ⟨hlow, hupp⟩
  constructor
  · unfold XiTimePart57bPressureSpectrumDiscreteConvexityData.excess
    have hlow' : (a : ℝ) * D.alphaStar + D.gStar ≤ D.P a := by
      simpa [foldGroundstateLowerBound] using hlow
    linarith
  · unfold XiTimePart57bPressureSpectrumDiscreteConvexityData.excess
    have hphi : foldGroundstateUpperBound a D.alphaStar =
        (a : ℝ) * D.alphaStar + Real.log Real.goldenRatio := by
      rfl
    rw [hphi] at hupp
    linarith

/-- Paper label: `thm:xi-time-part57b-pressure-spectrum-discrete-convexity-monotone-excess`.
Finite-volume log-convexity of the power sums yields discrete convexity of the limiting pressure
spectrum; the maximal-fiber comparison gives monotonic decay of the ground-state excess; and the
existing ground-state sandwich bounds transfer directly to the excess. -/
theorem paper_xi_time_part57b_pressure_spectrum_discrete_convexity_monotone_excess
    (D : XiTimePart57bPressureSpectrumDiscreteConvexityData) :
    D.discreteConvexity ∧ D.excessMonotone ∧ D.excessBounds := by
  exact
    ⟨xi_time_part57b_pressure_spectrum_discrete_convexity_monotone_excess_discrete_convexity D,
      xi_time_part57b_pressure_spectrum_discrete_convexity_monotone_excess_excess_monotone D,
      xi_time_part57b_pressure_spectrum_discrete_convexity_monotone_excess_excess_bounds D⟩

end Omega.Zeta
