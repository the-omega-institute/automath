import Mathlib

namespace Omega.Zeta

open Filter

/-- Concrete data for reducing the Lambert-W absolute-error estimate to its constant asymptotic
envelope.  The only asymptotic input is the eventual bound on the explicit error quotient. -/
structure xi_lambertw_constant_limsup_data where
  E : ℝ → ℝ
  T : ℕ → ℝ
  gamma : ℕ → ℝ
  n0 : ℕ
  mainCoeff : ℝ
  explicit_bound :
    ∀ n : ℕ, n0 ≤ n →
      |gamma n - T n| ≤ 2 * Real.pi * (E (2 * T n) + 1) /
        Real.log (T n / (4 * Real.pi))
  quotient_eventually_le :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        2 * Real.pi * (E (2 * T n) + 1) / Real.log (T n / (4 * Real.pi)) ≤
          2 * Real.pi * mainCoeff + ε

/-- Eventual epsilon form of the limsup constant claim. -/
def xi_lambertw_constant_limsup_data.statement
    (D : xi_lambertw_constant_limsup_data) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in atTop,
      |D.gamma n - D.T n| ≤ 2 * Real.pi * D.mainCoeff + ε

/-- Paper label: `cor:xi-lambertW-constant-limsup`.  The constant limsup certificate follows
by combining the explicit Lambert-W bound with the eventual vanishing of the lower-order quotient
terms. -/
theorem paper_xi_lambertw_constant_limsup (D : xi_lambertw_constant_limsup_data) :
    D.statement := by
  intro ε hε
  have hquot := D.quotient_eventually_le ε hε
  have hn0 : ∀ᶠ n : ℕ in atTop, D.n0 ≤ n := eventually_ge_atTop D.n0
  filter_upwards [hquot, hn0] with n hquot_n hn
  exact le_trans (D.explicit_bound n hn) hquot_n

end Omega.Zeta
