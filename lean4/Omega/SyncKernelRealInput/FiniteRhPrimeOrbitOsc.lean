import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.SyncKernelRealInput.RealInput40ResidueConstant

namespace Omega.SyncKernelRealInput

noncomputable section

/-- The Perron-scale base `λ = φ²` used in the finite RH prime-orbit normalization. -/
def finite_rh_prime_orbit_osc_lambda : ℝ :=
  real_input_40_residue_constant_lambda

/-- The `x`-scale corresponding to a length cutoff `N`. -/
def finite_rh_prime_orbit_osc_x (N : ℕ) : ℝ :=
  finite_rh_prime_orbit_osc_lambda ^ N

/-- The Perron main-term coefficient after passing from the `N`-scale to the `x = λ^N` scale. -/
def finite_rh_prime_orbit_osc_main_coeff : ℝ :=
  finite_rh_prime_orbit_osc_lambda * Real.log finite_rh_prime_orbit_osc_lambda /
    (finite_rh_prime_orbit_osc_lambda - 1)

/-- The odd critical-line frequency predicted by the `-sqrt λ` resonance. -/
def finite_rh_prime_orbit_osc_frequency (k : ℤ) : ℝ :=
  ((2 * (k : ℝ) + 1) * Real.pi) / Real.log finite_rh_prime_orbit_osc_lambda

/-- Paper label: `cor:finite-rh-prime-orbit-osc`. The audited Perron base is `λ = φ²`, its
square-root scale is the golden ratio itself, the passage from `N` to `x = λ^N` is logarithmic,
and the odd critical frequencies are spaced by the period `2π / log λ`. -/
theorem paper_finite_rh_prime_orbit_osc :
    finite_rh_prime_orbit_osc_lambda = Real.goldenRatio ^ (2 : ℕ) ∧
      Real.sqrt finite_rh_prime_orbit_osc_lambda = Real.goldenRatio ∧
      1 < finite_rh_prime_orbit_osc_lambda ∧
      0 < finite_rh_prime_orbit_osc_main_coeff ∧
      (∀ N : ℕ,
        Real.log (finite_rh_prime_orbit_osc_x N) =
          (N : ℝ) * Real.log finite_rh_prime_orbit_osc_lambda) ∧
      (∀ k : ℤ,
        finite_rh_prime_orbit_osc_frequency (k + 1) -
            finite_rh_prime_orbit_osc_frequency k =
          2 * Real.pi / Real.log finite_rh_prime_orbit_osc_lambda) := by
  have hlam_eq : finite_rh_prime_orbit_osc_lambda = Real.goldenRatio ^ (2 : ℕ) := by
    rfl
  have hphi_pos : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have hlam_gt1 : 1 < finite_rh_prime_orbit_osc_lambda := by
    rw [hlam_eq, Real.goldenRatio_sq]
    nlinarith [Real.one_lt_goldenRatio]
  have hlam_pos : 0 < finite_rh_prime_orbit_osc_lambda := lt_trans zero_lt_one hlam_gt1
  have hlog_pos : 0 < Real.log finite_rh_prime_orbit_osc_lambda := Real.log_pos hlam_gt1
  have hlog_ne : Real.log finite_rh_prime_orbit_osc_lambda ≠ 0 := hlog_pos.ne'
  refine ⟨hlam_eq, ?_, hlam_gt1, ?_, ?_, ?_⟩
  · calc
      Real.sqrt finite_rh_prime_orbit_osc_lambda = Real.sqrt (Real.goldenRatio ^ (2 : ℕ)) := by
        rw [hlam_eq]
      _ = |Real.goldenRatio| := by rw [Real.sqrt_sq_eq_abs]
      _ = Real.goldenRatio := abs_of_pos hphi_pos
  · unfold finite_rh_prime_orbit_osc_main_coeff
    exact div_pos (mul_pos hlam_pos hlog_pos) (by linarith [hlam_gt1])
  · intro N
    unfold finite_rh_prime_orbit_osc_x
    rw [show finite_rh_prime_orbit_osc_lambda ^ N = finite_rh_prime_orbit_osc_lambda ^ (N : ℝ) by
      rw [Real.rpow_natCast]]
    exact Real.log_rpow hlam_pos (N : ℝ)
  · intro k
    unfold finite_rh_prime_orbit_osc_frequency
    have hk :
        (2 * ((k + 1 : ℤ) : ℝ) + 1) - (2 * (k : ℝ) + 1) = 2 := by
      push_cast
      ring
    calc
      ((2 * ((k + 1 : ℤ) : ℝ) + 1) * Real.pi) / Real.log finite_rh_prime_orbit_osc_lambda -
          ((2 * (k : ℝ) + 1) * Real.pi) / Real.log finite_rh_prime_orbit_osc_lambda =
        (((2 * ((k + 1 : ℤ) : ℝ) + 1) - (2 * (k : ℝ) + 1)) * Real.pi) /
            Real.log finite_rh_prime_orbit_osc_lambda := by
              field_simp [hlog_ne]
      _ = 2 * Real.pi / Real.log finite_rh_prime_orbit_osc_lambda := by rw [hk]

end

end Omega.SyncKernelRealInput
