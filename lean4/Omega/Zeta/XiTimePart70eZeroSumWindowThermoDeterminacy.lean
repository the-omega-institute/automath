import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete finite-window data for the zero-sum thermo-determinacy identity. -/
structure xi_time_part70e_zero_sum_window_thermo_determinacy_data where
  window : ℕ
  rho : ℂ
  r : ℕ
  m : ℕ
  coeff : Fin (window + 1) → ℂ
  zero_sum : (∑ k : Fin (window + 1), coeff k) = 0

/-- The odd spectral frequency `2r - 1` attached to the window. -/
def xi_time_part70e_zero_sum_window_thermo_determinacy_frequency
    (D : xi_time_part70e_zero_sum_window_thermo_determinacy_data) : ℕ :=
  2 * D.r - 1

/-- Evaluation of the prefixed finite-window polynomial. -/
def xi_time_part70e_zero_sum_window_thermo_determinacy_eval
    (D : xi_time_part70e_zero_sum_window_thermo_determinacy_data) (z : ℂ) : ℂ :=
  ∑ k : Fin (D.window + 1), D.coeff k * z ^ (k : ℕ)

/-- The finite-window shift action on the exponential mode `rho^((2r-1)m)`. -/
def xi_time_part70e_zero_sum_window_thermo_determinacy_shift_action
    (D : xi_time_part70e_zero_sum_window_thermo_determinacy_data) : ℂ :=
  ∑ k : Fin (D.window + 1),
    D.coeff k *
      D.rho ^
        (xi_time_part70e_zero_sum_window_thermo_determinacy_frequency D * (D.m + (k : ℕ)))

/-- The concrete statement: zero-sum cancellation at `1` and diagonal action on the mode. -/
def xi_time_part70e_zero_sum_window_thermo_determinacy_statement
    (D : xi_time_part70e_zero_sum_window_thermo_determinacy_data) : Prop :=
  xi_time_part70e_zero_sum_window_thermo_determinacy_eval D 1 = 0 ∧
    xi_time_part70e_zero_sum_window_thermo_determinacy_shift_action D =
      xi_time_part70e_zero_sum_window_thermo_determinacy_eval D
          (D.rho ^ xi_time_part70e_zero_sum_window_thermo_determinacy_frequency D) *
        D.rho ^ (xi_time_part70e_zero_sum_window_thermo_determinacy_frequency D * D.m)

/-- Paper label: `thm:xi-time-part70e-zero-sum-window-thermo-determinacy`. -/
theorem paper_xi_time_part70e_zero_sum_window_thermo_determinacy
    (D : xi_time_part70e_zero_sum_window_thermo_determinacy_data) :
    xi_time_part70e_zero_sum_window_thermo_determinacy_statement D := by
  constructor
  · rw [xi_time_part70e_zero_sum_window_thermo_determinacy_eval]
    simpa using D.zero_sum
  · rw [xi_time_part70e_zero_sum_window_thermo_determinacy_shift_action,
      xi_time_part70e_zero_sum_window_thermo_determinacy_eval]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro k _hk
    let a := xi_time_part70e_zero_sum_window_thermo_determinacy_frequency D
    change
      D.coeff k * D.rho ^ (a * (D.m + (k : ℕ))) =
        D.coeff k * (D.rho ^ a) ^ (k : ℕ) * D.rho ^ (a * D.m)
    calc
      D.coeff k * D.rho ^ (a * (D.m + (k : ℕ))) =
          D.coeff k * (D.rho ^ (a * D.m) * D.rho ^ (a * (k : ℕ))) := by
        rw [Nat.mul_add, pow_add]
      _ = D.coeff k * (D.rho ^ (a * (k : ℕ)) * D.rho ^ (a * D.m)) := by
        rw [mul_comm (D.rho ^ (a * D.m))]
      _ = D.coeff k * ((D.rho ^ a) ^ (k : ℕ) * D.rho ^ (a * D.m)) := by
        rw [pow_mul]
      _ = D.coeff k * (D.rho ^ a) ^ (k : ℕ) * D.rho ^ (a * D.m) := by
        ring

end

end Omega.Zeta
