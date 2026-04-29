import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The algebraic leading coefficient carried by the two Poisson--Cauchy traceless channels. -/
def xi_cauchy_poisson_two_channel_orthogonal_leading_constant (A B : ℝ) : ℝ :=
  A ^ 2 / 8 + B ^ 2 / 2

/-- The even traceless mode, normalized so that one half of its squared norm contributes
`A ^ 2 / 8` to the leading coefficient. -/
def xi_cauchy_poisson_two_channel_orthogonal_leading_even_mode (A : ℝ) : ℝ × ℝ :=
  (A / 2, 0)

/-- The odd traceless mode, normalized so that one half of its squared norm contributes
`B ^ 2 / 2` to the leading coefficient. -/
def xi_cauchy_poisson_two_channel_orthogonal_leading_odd_mode (B : ℝ) : ℝ × ℝ :=
  (0, B)

/-- The Euclidean pairing used by the two leading Poisson--Cauchy modes. -/
def xi_cauchy_poisson_two_channel_orthogonal_leading_pairing (u v : ℝ × ℝ) : ℝ :=
  u.1 * v.1 + u.2 * v.2

/-- The squared norm induced by the leading-mode pairing. -/
def xi_cauchy_poisson_two_channel_orthogonal_leading_sqnorm (u : ℝ × ℝ) : ℝ :=
  xi_cauchy_poisson_two_channel_orthogonal_leading_pairing u u

/-- Paper label: `thm:xi-cauchy-poisson-two-channel-orthogonal-leading`.
The two normalized traceless modes are orthogonal, and their quadratic energies add to the
Poisson--Cauchy leading coefficient. -/
def xi_cauchy_poisson_two_channel_orthogonal_leading_statement : Prop :=
  ∀ A B : ℝ,
    xi_cauchy_poisson_two_channel_orthogonal_leading_pairing
        (xi_cauchy_poisson_two_channel_orthogonal_leading_even_mode A)
        (xi_cauchy_poisson_two_channel_orthogonal_leading_odd_mode B) = 0 ∧
      xi_cauchy_poisson_two_channel_orthogonal_leading_constant A B =
        (xi_cauchy_poisson_two_channel_orthogonal_leading_sqnorm
            (xi_cauchy_poisson_two_channel_orthogonal_leading_even_mode A) +
          xi_cauchy_poisson_two_channel_orthogonal_leading_sqnorm
            (xi_cauchy_poisson_two_channel_orthogonal_leading_odd_mode B)) / 2 ∧
      xi_cauchy_poisson_two_channel_orthogonal_leading_constant A B =
        A ^ 2 / 8 + B ^ 2 / 2

theorem paper_xi_cauchy_poisson_two_channel_orthogonal_leading :
    xi_cauchy_poisson_two_channel_orthogonal_leading_statement := by
  intro A B
  constructor
  · simp [xi_cauchy_poisson_two_channel_orthogonal_leading_pairing,
      xi_cauchy_poisson_two_channel_orthogonal_leading_even_mode,
      xi_cauchy_poisson_two_channel_orthogonal_leading_odd_mode]
  constructor
  · simp [xi_cauchy_poisson_two_channel_orthogonal_leading_constant,
      xi_cauchy_poisson_two_channel_orthogonal_leading_sqnorm,
      xi_cauchy_poisson_two_channel_orthogonal_leading_pairing,
      xi_cauchy_poisson_two_channel_orthogonal_leading_even_mode,
      xi_cauchy_poisson_two_channel_orthogonal_leading_odd_mode]
    ring
  · rfl

end
end Omega.Zeta
