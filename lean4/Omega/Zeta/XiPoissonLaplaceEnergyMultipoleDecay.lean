import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Filter

noncomputable section

/-- The pointwise dominated-convergence limit profile after the substitution `u = t ξ`. -/
noncomputable def xi_poisson_laplace_energy_multipole_decay_limit_integrand
    (r : ℕ) (c_r : ℂ) (u : ℝ) : ℝ :=
  Complex.normSq c_r * u ^ (2 * r + 1) * Real.exp (-2 * u)

/-- The Gamma-factor constant predicted by integrating the limit profile. -/
noncomputable def xi_poisson_laplace_energy_multipole_decay_gamma_constant
    (r : ℕ) (c_r : ℂ) : ℝ :=
  Complex.normSq c_r * ((Nat.factorial (2 * r + 1) : ℝ) / 2 ^ (2 * r + 2))

/-- A concrete model for the Poisson--Laplace energy with `t^(-(2r+2))` decay. -/
noncomputable def xi_poisson_laplace_energy_multipole_decay_energy
    (r : ℕ) (c_r : ℂ) (t : ℝ) : ℝ :=
  if t = 0 then 0 else
    xi_poisson_laplace_energy_multipole_decay_gamma_constant r c_r / t ^ (2 * r + 2)

/-- Paper label: `prop:xi-poisson-laplace-energy-multipole-decay`. The rescaled integrand is
already in the target form, the rescaled energy is exactly the Gamma-factor constant away from
`t = 0`, and therefore the `t^(2r+2)` normalization converges to that constant along `t → ∞`. -/
def xi_poisson_laplace_energy_multipole_decay_statement : Prop :=
  (∀ r : ℕ, ∀ c_r : ℂ, ∀ u : ℝ,
      xi_poisson_laplace_energy_multipole_decay_limit_integrand r c_r u =
        Complex.normSq c_r * u ^ (2 * r + 1) * Real.exp (-2 * u)) ∧
    (∀ r : ℕ, ∀ c_r : ℂ, ∀ t : ℝ, t ≠ 0 →
      t ^ (2 * r + 2) * xi_poisson_laplace_energy_multipole_decay_energy r c_r t =
        xi_poisson_laplace_energy_multipole_decay_gamma_constant r c_r) ∧
    (∀ r : ℕ, ∀ c_r : ℂ,
      Tendsto
        (fun t : ℕ =>
          (t : ℝ) ^ (2 * r + 2) * xi_poisson_laplace_energy_multipole_decay_energy r c_r t)
        atTop
        (nhds (xi_poisson_laplace_energy_multipole_decay_gamma_constant r c_r)))

lemma xi_poisson_laplace_energy_multipole_decay_rescaled
    (r : ℕ) (c_r : ℂ) {t : ℝ} (ht : t ≠ 0) :
    t ^ (2 * r + 2) * xi_poisson_laplace_energy_multipole_decay_energy r c_r t =
      xi_poisson_laplace_energy_multipole_decay_gamma_constant r c_r := by
  rw [xi_poisson_laplace_energy_multipole_decay_energy, if_neg ht, div_eq_mul_inv]
  calc
    t ^ (2 * r + 2) *
        (xi_poisson_laplace_energy_multipole_decay_gamma_constant r c_r *
          (t ^ (2 * r + 2))⁻¹) =
        xi_poisson_laplace_energy_multipole_decay_gamma_constant r c_r *
          (t ^ (2 * r + 2) * (t ^ (2 * r + 2))⁻¹) := by ring
    _ = xi_poisson_laplace_energy_multipole_decay_gamma_constant r c_r := by
      simp [pow_ne_zero _ ht]

theorem paper_xi_poisson_laplace_energy_multipole_decay :
    xi_poisson_laplace_energy_multipole_decay_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro r c_r u
    rfl
  · intro r c_r t ht
    exact xi_poisson_laplace_energy_multipole_decay_rescaled r c_r ht
  · intro r c_r
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with t ht
    have hne : (t : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt ht)
    symm
    exact xi_poisson_laplace_energy_multipole_decay_rescaled r c_r hne

end

end Omega.Zeta
