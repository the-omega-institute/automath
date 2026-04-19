import Mathlib

namespace Omega.EA

/-- A concrete one-sided oscillation surrogate at scale `δ`. For a differentiable readout, this is
enough to capture the `O(δ)` bound needed for the paper-facing nondifferentiability criterion. -/
noncomputable def osc (Y : Real -> Real) (t delta : Real) : Real :=
  2 * |Y (t + delta) - Y t|

/-- Differentiability at `t` yields a local linear oscillation bound.
    prop:groupoid-zeckendorf-visible-holder-nondifferentiability -/
theorem paper_groupoid_zeckendorf_visible_holder_nondifferentiability
    (Y : Real -> Real) (t : Real) (hderiv : DifferentiableAt Real Y t) :
    exists C delta0 : Real,
      0 < C /\
        0 < delta0 /\
          forall delta : Real,
            0 < delta ->
              delta <= delta0 -> osc Y t delta <= C * delta := by
  let D := deriv Y t
  have hlittle :
      (fun h : Real => Y (t + h) - Y t - h * D) =o[nhds 0] fun h => h := by
    simpa [D, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (hasDerivAt_iff_isLittleO_nhds_zero.mp hderiv.hasDerivAt)
  have hbound :
      ∀ᶠ h in nhds (0 : Real), |Y (t + h) - Y t - h * D| ≤ |h| := by
    simpa [Asymptotics.IsBigOWith, Real.norm_eq_abs] using (hlittle.def' zero_lt_one).bound
  obtain ⟨r, hrpos, hr⟩ := Metric.eventually_nhds_iff.1 hbound
  refine ⟨2 * (|D| + 1), r / 2, ?_⟩
  constructor
  · positivity
  constructor
  · positivity
  · intro delta hdelta_pos hdelta_le
    have hdelta_lt_r : delta < r := by
      linarith
    have hmem : delta ∈ Metric.ball (0 : Real) r := by
      simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hdelta_pos] using hdelta_lt_r
    have herr : |Y (t + delta) - Y t - delta * D| ≤ |delta| := hr hmem
    have habs :
        |Y (t + delta) - Y t| <= |delta * D| + |Y (t + delta) - Y t - delta * D| := by
      have hsplit :
          Y (t + delta) - Y t =
            delta * D + (Y (t + delta) - Y t - delta * D) := by ring
      have hEqAbs :
          |Y (t + delta) - Y t| = |delta * D + (Y (t + delta) - Y t - delta * D)| := by
        simpa using congrArg abs hsplit
      rw [hEqAbs]
      exact abs_add_le _ _
    have hmain : |Y (t + delta) - Y t| <= (|D| + 1) * delta := by
      have hdelta_abs : |delta| = delta := abs_of_pos hdelta_pos
      calc
        |Y (t + delta) - Y t|
            <= |delta * D| + |Y (t + delta) - Y t - delta * D| := habs
        _ <= |delta * D| + |delta| := add_le_add le_rfl herr
        _ = delta * |D| + delta := by
              simpa [abs_mul, hdelta_abs]
        _ = (|D| + 1) * delta := by ring
    calc
      osc Y t delta = 2 * |Y (t + delta) - Y t| := rfl
      _ <= 2 * ((|D| + 1) * delta) := by
            gcongr
      _ = (2 * (|D| + 1)) * delta := by ring

end Omega.EA
