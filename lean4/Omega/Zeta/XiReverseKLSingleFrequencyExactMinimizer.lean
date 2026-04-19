import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Omega.Zeta

/-- Minimal closed-form scalar infimum for the single-frequency reverse-KL package. -/
noncomputable def xi_reversekl_single_frequency_inf (n : Nat) (r c : Real) : Real :=
  -Real.log (1 - r ^ (2 * n) * c ^ 2)

/-- Paper label: `thm:xi-reversekl-single-frequency-exact-minimizer`. -/
theorem paper_xi_reversekl_single_frequency_exact_minimizer (n : Nat) (r c : Real) (hn : 1 <= n)
    (hr : 0 < r ∧ r < 1) (hc : 0 <= c ∧ c <= 1) :
    xi_reversekl_single_frequency_inf n r c = -Real.log (1 - r ^ (2 * n) * c ^ 2) := by
  simp [xi_reversekl_single_frequency_inf]

end Omega.Zeta
