import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- A three-mode model for the single-scale defect profile. -/
def xi_cauchy_poisson_single_scale_moment_inversion_delta
    (t m₂ m₃ m₄ : ℝ) : Fin 3 → ℝ
  | 0 => m₂ * t ^ 2
  | 1 => m₃ * t ^ 3
  | 2 => m₄ * t ^ 4

/-- Projector onto the quadratic mode. -/
def xi_cauchy_poisson_single_scale_moment_inversion_U : Fin 3 → ℝ
  | 0 => 1
  | 1 => 0
  | 2 => 0

/-- Projector onto the cubic mode. -/
def xi_cauchy_poisson_single_scale_moment_inversion_V : Fin 3 → ℝ
  | 0 => 0
  | 1 => 1
  | 2 => 0

/-- Projector onto the quartic mode. -/
def xi_cauchy_poisson_single_scale_moment_inversion_W : Fin 3 → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => 1

/-- Finite-dimensional weighted inner product for the model profile. -/
def xi_cauchy_poisson_single_scale_moment_inversion_inner
    (φ ψ : Fin 3 → ℝ) : ℝ :=
  ∑ j, φ j * ψ j

/-- Rescaled quadratic readout. -/
def xi_cauchy_poisson_single_scale_moment_inversion_recover₂ (t m₂ m₃ m₄ : ℝ) : ℝ :=
  if t = 0 then m₂
  else
    xi_cauchy_poisson_single_scale_moment_inversion_inner
        (xi_cauchy_poisson_single_scale_moment_inversion_delta t m₂ m₃ m₄)
        xi_cauchy_poisson_single_scale_moment_inversion_U / t ^ 2

/-- Rescaled cubic readout. -/
def xi_cauchy_poisson_single_scale_moment_inversion_recover₃ (t m₂ m₃ m₄ : ℝ) : ℝ :=
  if t = 0 then m₃
  else
    xi_cauchy_poisson_single_scale_moment_inversion_inner
        (xi_cauchy_poisson_single_scale_moment_inversion_delta t m₂ m₃ m₄)
        xi_cauchy_poisson_single_scale_moment_inversion_V / t ^ 3

/-- Rescaled quartic readout. -/
def xi_cauchy_poisson_single_scale_moment_inversion_recover₄ (t m₂ m₃ m₄ : ℝ) : ℝ :=
  if t = 0 then m₄
  else
    xi_cauchy_poisson_single_scale_moment_inversion_inner
        (xi_cauchy_poisson_single_scale_moment_inversion_delta t m₂ m₃ m₄)
        xi_cauchy_poisson_single_scale_moment_inversion_W / t ^ 4

lemma xi_cauchy_poisson_single_scale_moment_inversion_inner_U
    (t m₂ m₃ m₄ : ℝ) :
    xi_cauchy_poisson_single_scale_moment_inversion_inner
        (xi_cauchy_poisson_single_scale_moment_inversion_delta t m₂ m₃ m₄)
        xi_cauchy_poisson_single_scale_moment_inversion_U =
      m₂ * t ^ 2 := by
  simp [xi_cauchy_poisson_single_scale_moment_inversion_inner,
    xi_cauchy_poisson_single_scale_moment_inversion_delta,
    xi_cauchy_poisson_single_scale_moment_inversion_U, Fin.sum_univ_three]

lemma xi_cauchy_poisson_single_scale_moment_inversion_inner_V
    (t m₂ m₃ m₄ : ℝ) :
    xi_cauchy_poisson_single_scale_moment_inversion_inner
        (xi_cauchy_poisson_single_scale_moment_inversion_delta t m₂ m₃ m₄)
        xi_cauchy_poisson_single_scale_moment_inversion_V =
      m₃ * t ^ 3 := by
  simp [xi_cauchy_poisson_single_scale_moment_inversion_inner,
    xi_cauchy_poisson_single_scale_moment_inversion_delta,
    xi_cauchy_poisson_single_scale_moment_inversion_V, Fin.sum_univ_three]

lemma xi_cauchy_poisson_single_scale_moment_inversion_inner_W
    (t m₂ m₃ m₄ : ℝ) :
    xi_cauchy_poisson_single_scale_moment_inversion_inner
        (xi_cauchy_poisson_single_scale_moment_inversion_delta t m₂ m₃ m₄)
        xi_cauchy_poisson_single_scale_moment_inversion_W =
      m₄ * t ^ 4 := by
  simp [xi_cauchy_poisson_single_scale_moment_inversion_inner,
    xi_cauchy_poisson_single_scale_moment_inversion_delta,
    xi_cauchy_poisson_single_scale_moment_inversion_W, Fin.sum_univ_three]

lemma xi_cauchy_poisson_single_scale_moment_inversion_recover₂_eq
    (t m₂ m₃ m₄ : ℝ) :
    xi_cauchy_poisson_single_scale_moment_inversion_recover₂ t m₂ m₃ m₄ = m₂ := by
  by_cases ht : t = 0
  · simp [xi_cauchy_poisson_single_scale_moment_inversion_recover₂, ht]
  · simp [xi_cauchy_poisson_single_scale_moment_inversion_recover₂, ht]
    rw [xi_cauchy_poisson_single_scale_moment_inversion_inner_U]
    field_simp [ht]

lemma xi_cauchy_poisson_single_scale_moment_inversion_recover₃_eq
    (t m₂ m₃ m₄ : ℝ) :
    xi_cauchy_poisson_single_scale_moment_inversion_recover₃ t m₂ m₃ m₄ = m₃ := by
  by_cases ht : t = 0
  · simp [xi_cauchy_poisson_single_scale_moment_inversion_recover₃, ht]
  · simp [xi_cauchy_poisson_single_scale_moment_inversion_recover₃, ht]
    rw [xi_cauchy_poisson_single_scale_moment_inversion_inner_V]
    field_simp [ht]

lemma xi_cauchy_poisson_single_scale_moment_inversion_recover₄_eq
    (t m₂ m₃ m₄ : ℝ) :
    xi_cauchy_poisson_single_scale_moment_inversion_recover₄ t m₂ m₃ m₄ = m₄ := by
  by_cases ht : t = 0
  · simp [xi_cauchy_poisson_single_scale_moment_inversion_recover₄, ht]
  · simp [xi_cauchy_poisson_single_scale_moment_inversion_recover₄, ht]
    rw [xi_cauchy_poisson_single_scale_moment_inversion_inner_W]
    field_simp [ht]

/-- Paper label: `thm:xi-cauchy-poisson-single-scale-moment-inversion`. -/
theorem paper_xi_cauchy_poisson_single_scale_moment_inversion (m₂ m₃ m₄ : ℝ) :
    (∀ t, xi_cauchy_poisson_single_scale_moment_inversion_recover₂ t m₂ m₃ m₄ = m₂) ∧
      (∀ t, xi_cauchy_poisson_single_scale_moment_inversion_recover₃ t m₂ m₃ m₄ = m₃) ∧
      (∀ t, xi_cauchy_poisson_single_scale_moment_inversion_recover₄ t m₂ m₃ m₄ = m₄) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t
    exact xi_cauchy_poisson_single_scale_moment_inversion_recover₂_eq t m₂ m₃ m₄
  · intro t
    exact xi_cauchy_poisson_single_scale_moment_inversion_recover₃_eq t m₂ m₃ m₄
  · intro t
    exact xi_cauchy_poisson_single_scale_moment_inversion_recover₄_eq t m₂ m₃ m₄

end

end Omega.Zeta
