import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Boolean register bit as a rational observable. -/
def xi_time_part9xaba_window6_d2_slice_unique_local_interaction_bit (b : Bool) : ℚ :=
  if b then 1 else 0

/-- The three single-site hidden supports for the window-6 two-register model. -/
def xi_time_part9xaba_window6_d2_slice_unique_local_interaction_support :
    ℕ → Finset (Bool × Bool)
  | 2 => ({(false, false), (false, true)} : Finset (Bool × Bool))
  | 3 => ({(false, false), (true, false), (false, true)} : Finset (Bool × Bool))
  | 4 => Finset.univ
  | _ => ∅

/-- Uniform expectation of a rational observable on one of the finite supports. -/
def xi_time_part9xaba_window6_d2_slice_unique_local_interaction_expectation
    (d : ℕ) (f : Bool × Bool → ℚ) : ℚ :=
  match d with
  | 2 => (f (false, false) + f (false, true)) / 2
  | 3 => (f (false, false) + f (true, false) + f (false, true)) / 3
  | 4 => (f (false, false) + f (true, false) + f (false, true) + f (true, true)) / 4
  | _ => 0

/-- Uniform covariance of the two Boolean registers on a support. -/
def xi_time_part9xaba_window6_d2_slice_unique_local_interaction_covariance (d : ℕ) : ℚ :=
  xi_time_part9xaba_window6_d2_slice_unique_local_interaction_expectation d
      (fun p =>
        xi_time_part9xaba_window6_d2_slice_unique_local_interaction_bit p.1 *
          xi_time_part9xaba_window6_d2_slice_unique_local_interaction_bit p.2) -
    xi_time_part9xaba_window6_d2_slice_unique_local_interaction_expectation d
        (fun p => xi_time_part9xaba_window6_d2_slice_unique_local_interaction_bit p.1) *
      xi_time_part9xaba_window6_d2_slice_unique_local_interaction_expectation d
        (fun p => xi_time_part9xaba_window6_d2_slice_unique_local_interaction_bit p.2)

/-- Paper label: `prop:xi-time-part9xaba-window6-d2-slice-unique-local-interaction`.
The three finite Boolean-register supports have covariance `0`, `-1/9`, and `0`;
the zero-covariance layers are the product supports. -/
theorem paper_xi_time_part9xaba_window6_d2_slice_unique_local_interaction :
    xi_time_part9xaba_window6_d2_slice_unique_local_interaction_support 2 =
        (({false} : Finset Bool).product ({false, true} : Finset Bool)) ∧
      xi_time_part9xaba_window6_d2_slice_unique_local_interaction_support 3 =
        ({(false, false), (true, false), (false, true)} : Finset (Bool × Bool)) ∧
      xi_time_part9xaba_window6_d2_slice_unique_local_interaction_support 4 =
        ((Finset.univ : Finset Bool).product (Finset.univ : Finset Bool)) ∧
      xi_time_part9xaba_window6_d2_slice_unique_local_interaction_covariance 2 = 0 ∧
      xi_time_part9xaba_window6_d2_slice_unique_local_interaction_covariance 3 = -(1 / 9) ∧
      xi_time_part9xaba_window6_d2_slice_unique_local_interaction_covariance 4 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext p
    rcases p with ⟨a, b⟩
    cases a <;> cases b <;> decide
  · rfl
  · ext p
    rcases p with ⟨a, b⟩
    cases a <;> cases b <;> decide
  · norm_num [xi_time_part9xaba_window6_d2_slice_unique_local_interaction_support,
      xi_time_part9xaba_window6_d2_slice_unique_local_interaction_covariance,
      xi_time_part9xaba_window6_d2_slice_unique_local_interaction_expectation,
      xi_time_part9xaba_window6_d2_slice_unique_local_interaction_bit]
  · norm_num [xi_time_part9xaba_window6_d2_slice_unique_local_interaction_support,
      xi_time_part9xaba_window6_d2_slice_unique_local_interaction_covariance,
      xi_time_part9xaba_window6_d2_slice_unique_local_interaction_expectation,
      xi_time_part9xaba_window6_d2_slice_unique_local_interaction_bit]
  · norm_num [xi_time_part9xaba_window6_d2_slice_unique_local_interaction_support,
      xi_time_part9xaba_window6_d2_slice_unique_local_interaction_covariance,
      xi_time_part9xaba_window6_d2_slice_unique_local_interaction_expectation,
      xi_time_part9xaba_window6_d2_slice_unique_local_interaction_bit]

end Omega.Zeta
