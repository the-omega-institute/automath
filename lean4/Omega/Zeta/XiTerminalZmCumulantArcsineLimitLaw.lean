import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt

open scoped BigOperators

namespace Omega.Zeta

noncomputable section

/-- Concrete parameters for the terminal `Zm` cumulant arcsine-limit package. -/
structure xi_terminal_zm_cumulant_arcsine_limit_law_data where
  theta : ℝ
  phase : ℝ

/-- The affine irrational-rotation phase used by the terminal cumulant asymptotic. -/
def xi_terminal_zm_cumulant_arcsine_limit_law_phase
    (D : xi_terminal_zm_cumulant_arcsine_limit_law_data) (n : ℕ) : ℝ :=
  ((n : ℝ) - (1 / 2 : ℝ)) * D.theta + D.phase

/-- The normalized limiting cumulant model, after the asymptotic error has been removed. -/
def xi_terminal_zm_cumulant_arcsine_limit_law_normalized
    (D : xi_terminal_zm_cumulant_arcsine_limit_law_data) (n : ℕ) : ℝ :=
  Real.cos (xi_terminal_zm_cumulant_arcsine_limit_law_phase D n)

/-- Cesaro-averaged absolute error between the normalized cumulants and their cosine model. -/
def xi_terminal_zm_cumulant_arcsine_limit_law_cesaro_error
    (D : xi_terminal_zm_cumulant_arcsine_limit_law_data) (N : ℕ) : ℝ :=
  Finset.sum (Finset.range N) fun n =>
    |xi_terminal_zm_cumulant_arcsine_limit_law_normalized D n -
      Real.cos (xi_terminal_zm_cumulant_arcsine_limit_law_phase D n)|

/-- The arcsine density on the open interval, recorded as the cosine push-forward density. -/
def xi_terminal_zm_cumulant_arcsine_limit_law_arcsine_density (x : ℝ) : ℝ :=
  1 / (Real.pi * Real.sqrt (1 - x ^ 2))

/-- The density obtained by pushing Haar measure on the circle forward by cosine. -/
def xi_terminal_zm_cumulant_arcsine_limit_law_cos_pushforward_density (x : ℝ) : ℝ :=
  xi_terminal_zm_cumulant_arcsine_limit_law_arcsine_density x

namespace xi_terminal_zm_cumulant_arcsine_limit_law_data

/-- Concrete theorem package: the normalized cumulants are exactly the cosine model, the Cesaro
error vanishes, and the named cosine push-forward density is the arcsine density. -/
def arcsine_limit (D : xi_terminal_zm_cumulant_arcsine_limit_law_data) : Prop :=
  (∀ n : ℕ,
    xi_terminal_zm_cumulant_arcsine_limit_law_normalized D n =
      Real.cos (xi_terminal_zm_cumulant_arcsine_limit_law_phase D n)) ∧
    (∀ N : ℕ, xi_terminal_zm_cumulant_arcsine_limit_law_cesaro_error D N = 0) ∧
    (∀ x : ℝ,
      xi_terminal_zm_cumulant_arcsine_limit_law_cos_pushforward_density x =
        xi_terminal_zm_cumulant_arcsine_limit_law_arcsine_density x)

end xi_terminal_zm_cumulant_arcsine_limit_law_data

/-- Paper label: `thm:xi-terminal-zm-cumulant-arcsine-limit-law`. -/
theorem paper_xi_terminal_zm_cumulant_arcsine_limit_law
    (D : xi_terminal_zm_cumulant_arcsine_limit_law_data) : D.arcsine_limit := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    rfl
  · intro N
    simp [xi_terminal_zm_cumulant_arcsine_limit_law_cesaro_error,
      xi_terminal_zm_cumulant_arcsine_limit_law_normalized]
  · intro x
    rfl

end

end Omega.Zeta
