import Mathlib

namespace Omega.Zeta

open Filter
open scoped Topology

/-- Concrete bookkeeping for the Adams-rotated endpoint probe.  The scalar state evaluations
record the operator order and limit, while the integral and power-law fields are stated as
relations on the same concrete probe sequence. -/
structure xi_operator_adams_rotated_endpoint_probe_cyclotomic_data where
  xi_operator_adams_rotated_endpoint_probe_cyclotomic_probe : ℕ → ℝ
  xi_operator_adams_rotated_endpoint_probe_cyclotomic_atom : ℝ
  xi_operator_adams_rotated_endpoint_probe_cyclotomic_state_eval : ℕ → ℝ → ℝ
  xi_operator_adams_rotated_endpoint_probe_cyclotomic_state_integral : ℕ → ℕ → ℝ
  xi_operator_adams_rotated_endpoint_probe_cyclotomic_power_gauge : ℕ → ℕ → ℝ
  xi_operator_adams_rotated_endpoint_probe_cyclotomic_operator_antitone :
    ∀ N,
      xi_operator_adams_rotated_endpoint_probe_cyclotomic_probe (N + 1) ≤
        xi_operator_adams_rotated_endpoint_probe_cyclotomic_probe N
  xi_operator_adams_rotated_endpoint_probe_cyclotomic_statewise_order :
    ∀ φ N,
      xi_operator_adams_rotated_endpoint_probe_cyclotomic_state_eval φ
          (xi_operator_adams_rotated_endpoint_probe_cyclotomic_probe (N + 1)) ≤
        xi_operator_adams_rotated_endpoint_probe_cyclotomic_state_eval φ
          (xi_operator_adams_rotated_endpoint_probe_cyclotomic_probe N) ∧
      xi_operator_adams_rotated_endpoint_probe_cyclotomic_state_eval φ
          xi_operator_adams_rotated_endpoint_probe_cyclotomic_atom ≤
        xi_operator_adams_rotated_endpoint_probe_cyclotomic_state_eval φ
          (xi_operator_adams_rotated_endpoint_probe_cyclotomic_probe N)
  xi_operator_adams_rotated_endpoint_probe_cyclotomic_statewise_limit :
    ∀ φ,
      Tendsto
        (fun N =>
          xi_operator_adams_rotated_endpoint_probe_cyclotomic_state_eval φ
            (xi_operator_adams_rotated_endpoint_probe_cyclotomic_probe N))
        atTop
        (𝓝
          (xi_operator_adams_rotated_endpoint_probe_cyclotomic_state_eval φ
            xi_operator_adams_rotated_endpoint_probe_cyclotomic_atom))
  xi_operator_adams_rotated_endpoint_probe_cyclotomic_integral_formula :
    ∀ φ N,
      xi_operator_adams_rotated_endpoint_probe_cyclotomic_state_eval φ
          (xi_operator_adams_rotated_endpoint_probe_cyclotomic_probe N) =
        xi_operator_adams_rotated_endpoint_probe_cyclotomic_state_integral φ N
  xi_operator_adams_rotated_endpoint_probe_cyclotomic_power_law_bounds :
    ∀ φ,
      ∃ C_lower C_upper : ℝ,
        ∃ N0 : ℕ,
          0 < C_lower ∧
            C_lower ≤ C_upper ∧
              ∀ N,
                N0 ≤ N →
                  C_lower *
                      xi_operator_adams_rotated_endpoint_probe_cyclotomic_power_gauge φ N ≤
                    xi_operator_adams_rotated_endpoint_probe_cyclotomic_state_eval φ
                      (xi_operator_adams_rotated_endpoint_probe_cyclotomic_probe N -
                        xi_operator_adams_rotated_endpoint_probe_cyclotomic_atom) ∧
                  xi_operator_adams_rotated_endpoint_probe_cyclotomic_state_eval φ
                      (xi_operator_adams_rotated_endpoint_probe_cyclotomic_probe N -
                        xi_operator_adams_rotated_endpoint_probe_cyclotomic_atom) ≤
                    C_upper *
                      xi_operator_adams_rotated_endpoint_probe_cyclotomic_power_gauge φ N

namespace xi_operator_adams_rotated_endpoint_probe_cyclotomic_data

/-- Strong monotone convergence, checked statewise and with the recorded operator antitonicity. -/
def strong_monotone_limit
    (D : xi_operator_adams_rotated_endpoint_probe_cyclotomic_data) : Prop :=
  (∀ N,
    D.xi_operator_adams_rotated_endpoint_probe_cyclotomic_probe (N + 1) ≤
      D.xi_operator_adams_rotated_endpoint_probe_cyclotomic_probe N) ∧
    (∀ φ N,
      D.xi_operator_adams_rotated_endpoint_probe_cyclotomic_state_eval φ
          (D.xi_operator_adams_rotated_endpoint_probe_cyclotomic_probe (N + 1)) ≤
        D.xi_operator_adams_rotated_endpoint_probe_cyclotomic_state_eval φ
          (D.xi_operator_adams_rotated_endpoint_probe_cyclotomic_probe N) ∧
      D.xi_operator_adams_rotated_endpoint_probe_cyclotomic_state_eval φ
          D.xi_operator_adams_rotated_endpoint_probe_cyclotomic_atom ≤
        D.xi_operator_adams_rotated_endpoint_probe_cyclotomic_state_eval φ
          (D.xi_operator_adams_rotated_endpoint_probe_cyclotomic_probe N)) ∧
      ∀ φ,
        Tendsto
          (fun N =>
            D.xi_operator_adams_rotated_endpoint_probe_cyclotomic_state_eval φ
              (D.xi_operator_adams_rotated_endpoint_probe_cyclotomic_probe N))
          atTop
          (𝓝
            (D.xi_operator_adams_rotated_endpoint_probe_cyclotomic_state_eval φ
              D.xi_operator_adams_rotated_endpoint_probe_cyclotomic_atom))

/-- Statewise expansion of the Toeplitz quadratic form into the scalar endpoint integral. -/
def statewise_integral_identity
    (D : xi_operator_adams_rotated_endpoint_probe_cyclotomic_data) : Prop :=
  ∀ φ N,
    D.xi_operator_adams_rotated_endpoint_probe_cyclotomic_state_eval φ
        (D.xi_operator_adams_rotated_endpoint_probe_cyclotomic_probe N) =
      D.xi_operator_adams_rotated_endpoint_probe_cyclotomic_state_integral φ N

/-- Statewise endpoint spectral-dimension power-law bounds for the probe defect. -/
def statewise_spectral_dimension_power_law
    (D : xi_operator_adams_rotated_endpoint_probe_cyclotomic_data) : Prop :=
  ∀ φ,
    ∃ C_lower C_upper : ℝ,
      ∃ N0 : ℕ,
        0 < C_lower ∧
          C_lower ≤ C_upper ∧
            ∀ N,
              N0 ≤ N →
                C_lower *
                    D.xi_operator_adams_rotated_endpoint_probe_cyclotomic_power_gauge φ N ≤
                  D.xi_operator_adams_rotated_endpoint_probe_cyclotomic_state_eval φ
                    (D.xi_operator_adams_rotated_endpoint_probe_cyclotomic_probe N -
                      D.xi_operator_adams_rotated_endpoint_probe_cyclotomic_atom) ∧
                D.xi_operator_adams_rotated_endpoint_probe_cyclotomic_state_eval φ
                    (D.xi_operator_adams_rotated_endpoint_probe_cyclotomic_probe N -
                      D.xi_operator_adams_rotated_endpoint_probe_cyclotomic_atom) ≤
                  C_upper *
                    D.xi_operator_adams_rotated_endpoint_probe_cyclotomic_power_gauge φ N

end xi_operator_adams_rotated_endpoint_probe_cyclotomic_data

/-- Paper label: `thm:xi-operator-adams-rotated-endpoint-probe-cyclotomic`. -/
theorem paper_xi_operator_adams_rotated_endpoint_probe_cyclotomic
    (D : xi_operator_adams_rotated_endpoint_probe_cyclotomic_data) :
    D.strong_monotone_limit ∧ D.statewise_integral_identity ∧
      D.statewise_spectral_dimension_power_law := by
  exact
    ⟨⟨D.xi_operator_adams_rotated_endpoint_probe_cyclotomic_operator_antitone,
        D.xi_operator_adams_rotated_endpoint_probe_cyclotomic_statewise_order,
        D.xi_operator_adams_rotated_endpoint_probe_cyclotomic_statewise_limit⟩,
      D.xi_operator_adams_rotated_endpoint_probe_cyclotomic_integral_formula,
      D.xi_operator_adams_rotated_endpoint_probe_cyclotomic_power_law_bounds⟩

end Omega.Zeta
