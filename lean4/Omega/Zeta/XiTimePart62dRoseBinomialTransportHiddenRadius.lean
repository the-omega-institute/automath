import Mathlib
import Omega.Zeta.TwoScaleBinomialTransportSingularCircle

namespace Omega.Zeta

open Complex

/-- The rose binomial transport `F_{n,d}(z) = (z^(d+n)+z^(d-n))/2`. -/
noncomputable def xi_time_part62d_rose_binomial_transport_hidden_radius_transport
    (n d : ℕ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (z ^ (d + n) + z ^ (d - n))

/-- Euler-form rose parametrization after putting the common `e^{iθ}` factor outside. -/
noncomputable def xi_time_part62d_rose_binomial_transport_hidden_radius_eulerForm
    (n d : ℕ) (θ : ℝ) : ℂ :=
  let a : ℝ := ((n : ℝ) / (d : ℝ)) * θ
  (1 / 2 : ℂ) *
      (Complex.exp ((a : ℂ) * Complex.I) +
        Complex.exp ((-a : ℝ) * Complex.I)) *
    Complex.exp (θ * Complex.I)

/-- The trigonometric rose parametrization `cos ((n/d)θ) e^{iθ}`. -/
noncomputable def xi_time_part62d_rose_binomial_transport_hidden_radius_trigForm
    (n d : ℕ) (θ : ℝ) : ℂ :=
  let a : ℝ := ((n : ℝ) / (d : ℝ)) * θ
  (Real.cos a : ℂ) * Complex.exp (θ * Complex.I)

/-- Hidden-radius scalar written in the logarithmic/arctanh normalization. -/
noncomputable def xi_time_part62d_rose_binomial_transport_hidden_radius_radius
    (n d : ℕ) : ℝ :=
  Real.exp (-(1 / (n : ℝ) * Real.artanh ((n : ℝ) / (d : ℝ))))

/-- Concrete package for the rose transport identity, the inherited critical-circle package,
and the logarithmic hidden-radius normalization. -/
noncomputable def xi_time_part62d_rose_binomial_transport_hidden_radius_statement : Prop :=
  (∀ n d : ℕ, ∀ θ : ℝ,
      xi_time_part62d_rose_binomial_transport_hidden_radius_eulerForm n d θ =
        xi_time_part62d_rose_binomial_transport_hidden_radius_trigForm n d θ) ∧
    (∀ n d : ℕ,
      1 ≤ n →
        n < d →
          xi_time_part62d_two_scale_binomial_transport_singular_circle_positive_n_criticalEquation
            (d + n) (d - n) (1 / 2 : ℂ) (1 / 2 : ℂ)) ∧
    (∀ n d : ℕ,
      1 ≤ n →
        n < d →
          xi_time_part62d_two_scale_binomial_transport_singular_circle_sameRadius
            (d + n) (d - n) (1 / 2 : ℂ) (1 / 2 : ℂ)) ∧
    (∀ n d : ℕ,
      1 ≤ n →
        n < d →
          Real.log (1 / xi_time_part62d_rose_binomial_transport_hidden_radius_radius n d) =
            1 / (n : ℝ) * Real.artanh ((n : ℝ) / (d : ℝ)))

private lemma xi_time_part62d_rose_binomial_transport_hidden_radius_euler_identity
    (n d : ℕ) (θ : ℝ) :
    xi_time_part62d_rose_binomial_transport_hidden_radius_eulerForm n d θ =
      xi_time_part62d_rose_binomial_transport_hidden_radius_trigForm n d θ := by
  let a : ℝ := ((n : ℝ) / (d : ℝ)) * θ
  have hhalf :
      (1 / 2 : ℂ) *
          (Complex.exp ((a : ℂ) * Complex.I) + Complex.exp ((-a : ℝ) * Complex.I)) =
        (Real.cos a : ℂ) := by
    have htwo := Complex.two_cos (a : ℂ)
    have htwo' :
        2 * Complex.cos (a : ℂ) =
          Complex.exp ((a : ℂ) * Complex.I) + Complex.exp ((-a : ℝ) * Complex.I) := by
      simpa using htwo
    rw [Complex.ofReal_cos, ← htwo']
    ring
  dsimp [xi_time_part62d_rose_binomial_transport_hidden_radius_eulerForm,
    xi_time_part62d_rose_binomial_transport_hidden_radius_trigForm]
  change
    ((1 / 2 : ℂ) *
        (Complex.exp ((a : ℂ) * Complex.I) + Complex.exp ((-a : ℝ) * Complex.I))) *
      Complex.exp (θ * Complex.I) =
        (Real.cos a : ℂ) * Complex.exp (θ * Complex.I)
  rw [hhalf]

private lemma xi_time_part62d_rose_binomial_transport_hidden_radius_log_radius
    (n d : ℕ) :
    Real.log (1 / xi_time_part62d_rose_binomial_transport_hidden_radius_radius n d) =
      1 / (n : ℝ) * Real.artanh ((n : ℝ) / (d : ℝ)) := by
  simp [xi_time_part62d_rose_binomial_transport_hidden_radius_radius, div_eq_mul_inv,
    Real.exp_neg]

/-- Paper label: `cor:xi-time-part62d-rose-binomial-transport-hidden-radius`. -/
theorem paper_xi_time_part62d_rose_binomial_transport_hidden_radius :
    xi_time_part62d_rose_binomial_transport_hidden_radius_statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact xi_time_part62d_rose_binomial_transport_hidden_radius_euler_identity
  · intro n d hn hnd
    have hmn : d - n < d + n := by omega
    have hα : (1 / 2 : ℂ) ≠ 0 := by norm_num
    have hβ : (1 / 2 : ℂ) ≠ 0 := by norm_num
    exact (paper_xi_time_part62d_two_scale_binomial_transport_singular_circle
      (d + n) (d - n) (1 / 2 : ℂ) (1 / 2 : ℂ) hmn hα hβ).2.1
  · intro n d hn hnd
    have hmn : d - n < d + n := by omega
    have hα : (1 / 2 : ℂ) ≠ 0 := by norm_num
    have hβ : (1 / 2 : ℂ) ≠ 0 := by norm_num
    exact (paper_xi_time_part62d_two_scale_binomial_transport_singular_circle
      (d + n) (d - n) (1 / 2 : ℂ) (1 / 2 : ℂ) hmn hα hβ).2.2
  · intro n d hn hnd
    exact xi_time_part62d_rose_binomial_transport_hidden_radius_log_radius n d

end Omega.Zeta
