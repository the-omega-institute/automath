import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete datum for the zero-dispersion constant-bias inverse curve. -/
structure xi_constant_bias_inversion_b_eps_data where
  xi_constant_bias_inversion_b_eps_sc : ℝ
  xi_constant_bias_inversion_b_eps_mid_branch : ℝ → ℝ
  xi_constant_bias_inversion_b_eps_low_branch : ℝ → ℝ

namespace xi_constant_bias_inversion_b_eps_data

/-- The piecewise inverse constant term `b(ε)`, written in terms of `s = 1 - ε`. -/
noncomputable def xi_constant_bias_inversion_b_eps_b (D : xi_constant_bias_inversion_b_eps_data)
    (ε : ℝ) : ℝ :=
  let s := 1 - ε
  if s = 1 then
    0
  else if D.xi_constant_bias_inversion_b_eps_sc ≤ s then
    D.xi_constant_bias_inversion_b_eps_mid_branch s
  else
    D.xi_constant_bias_inversion_b_eps_low_branch s

end xi_constant_bias_inversion_b_eps_data

/-- Paper label: `cor:xi-constant-bias-inversion-b-eps`. -/
theorem paper_xi_constant_bias_inversion_b_eps (D : xi_constant_bias_inversion_b_eps_data) :
    ∀ ε,
      let s := 1 - ε
      D.xi_constant_bias_inversion_b_eps_b ε =
        if s = 1 then
          0
        else if D.xi_constant_bias_inversion_b_eps_sc ≤ s then
          D.xi_constant_bias_inversion_b_eps_mid_branch s
        else
          D.xi_constant_bias_inversion_b_eps_low_branch s := by
  intro ε
  rfl

end Omega.Zeta
