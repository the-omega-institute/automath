import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Concrete finite defect-packet model for the offline Neumann Cauchy semigroup package. -/
structure xi_offline_neumann_cauchy_semigroup_generator_data where
  κ : ℕ
  center : Fin κ → ℝ
  depth : Fin κ → ℝ
  weight : Fin κ → ℝ
  hdepth : ∀ j, 0 < depth j

namespace xi_offline_neumann_cauchy_semigroup_generator_data

/-- Shifted Cauchy kernel at depth `a`. -/
def xi_offline_neumann_cauchy_semigroup_generator_cauchy_kernel (a x : ℝ) : ℝ :=
  a / (x ^ 2 + a ^ 2)

/-- One evolved defect packet. -/
def xi_offline_neumann_cauchy_semigroup_generator_packet
    (D : xi_offline_neumann_cauchy_semigroup_generator_data) (a : ℝ) (j : Fin D.κ) (x : ℝ) : ℝ :=
  D.weight j *
    xi_offline_neumann_cauchy_semigroup_generator_cauchy_kernel (D.depth j + a) (x - D.center j)

/-- The explicit evolved Neumann trace. -/
def xi_offline_neumann_cauchy_semigroup_generator_trace
    (D : xi_offline_neumann_cauchy_semigroup_generator_data) (a x : ℝ) : ℝ :=
  2 * ∑ j : Fin D.κ, D.xi_offline_neumann_cauchy_semigroup_generator_packet a j x

/-- Fourier multiplier attached to the Cauchy semigroup. -/
def xi_offline_neumann_cauchy_semigroup_generator_multiplier (a ξ : ℝ) : ℝ :=
  Real.exp (-a * |ξ|)

/-- One Fourier packet. -/
def xi_offline_neumann_cauchy_semigroup_generator_fourier_packet
    (D : xi_offline_neumann_cauchy_semigroup_generator_data) (a : ℝ) (j : Fin D.κ) (ξ : ℝ) : ℝ :=
  D.weight j * Real.exp (-(D.depth j + a) * |ξ|) * Real.cos (D.center j * ξ)

/-- Fourier-side representation of the evolved trace. -/
def xi_offline_neumann_cauchy_semigroup_generator_fourier_trace
    (D : xi_offline_neumann_cauchy_semigroup_generator_data) (a ξ : ℝ) : ℝ :=
  2 * ∑ j : Fin D.κ, D.xi_offline_neumann_cauchy_semigroup_generator_fourier_packet a j ξ

/-- Fourier-side `a`-derivative of the evolved trace. -/
def xi_offline_neumann_cauchy_semigroup_generator_fourier_derivative
    (D : xi_offline_neumann_cauchy_semigroup_generator_data) (a ξ : ℝ) : ℝ :=
  2 * ∑ j : Fin D.κ,
    -D.weight j * |ξ| * Real.exp (-(D.depth j + a) * |ξ|) * Real.cos (D.center j * ξ)

/-- Fourier multiplier for the `(-Δ)^(1/2)` generator. -/
def xi_offline_neumann_cauchy_semigroup_generator_half_laplacian
    (D : xi_offline_neumann_cauchy_semigroup_generator_data) (a ξ : ℝ) : ℝ :=
  -|ξ| * D.xi_offline_neumann_cauchy_semigroup_generator_fourier_trace a ξ

/-- Paper-facing finite-packet package: semigroup recursion on the Fourier multiplier side, the
explicit `(δ_j + a)` Cauchy packet formula, and the `(-Δ)^(1/2)` generator identity. -/
def statement (D : xi_offline_neumann_cauchy_semigroup_generator_data) : Prop :=
  (∀ a b ξ : ℝ,
    D.xi_offline_neumann_cauchy_semigroup_generator_fourier_trace (a + b) ξ =
      xi_offline_neumann_cauchy_semigroup_generator_multiplier a ξ *
        D.xi_offline_neumann_cauchy_semigroup_generator_fourier_trace b ξ) ∧
    (∀ a x : ℝ,
      D.xi_offline_neumann_cauchy_semigroup_generator_trace a x =
        2 * ∑ j : Fin D.κ, D.xi_offline_neumann_cauchy_semigroup_generator_packet a j x) ∧
    (∀ a ξ : ℝ,
      D.xi_offline_neumann_cauchy_semigroup_generator_fourier_derivative a ξ =
        D.xi_offline_neumann_cauchy_semigroup_generator_half_laplacian a ξ)

end xi_offline_neumann_cauchy_semigroup_generator_data

open xi_offline_neumann_cauchy_semigroup_generator_data

/-- Paper label: `thm:xi-offline-neumann-cauchy-semigroup-generator`. -/
theorem paper_xi_offline_neumann_cauchy_semigroup_generator
    (D : xi_offline_neumann_cauchy_semigroup_generator_data) : D.statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b ξ
    calc
      D.xi_offline_neumann_cauchy_semigroup_generator_fourier_trace (a + b) ξ
          = 2 * ∑ j : Fin D.κ,
              D.weight j * Real.exp (-(D.depth j + (a + b)) * |ξ|) * Real.cos (D.center j * ξ) := by
            simp [xi_offline_neumann_cauchy_semigroup_generator_fourier_trace,
              xi_offline_neumann_cauchy_semigroup_generator_fourier_packet]
      _ = 2 * ∑ j : Fin D.κ,
            Real.exp (-a * |ξ|) *
              (D.weight j * Real.exp (-(D.depth j + b) * |ξ|) * Real.cos (D.center j * ξ)) := by
            congr 1
            apply Finset.sum_congr rfl
            intro j hj
            have hexp :
                Real.exp (-(D.depth j + (a + b)) * |ξ|) =
                  Real.exp (-a * |ξ|) * Real.exp (-(D.depth j + b) * |ξ|) := by
              rw [← Real.exp_add]
              congr 1
              ring
            calc
              D.weight j * Real.exp (-(D.depth j + (a + b)) * |ξ|) * Real.cos (D.center j * ξ)
                  = D.weight j *
                      (Real.exp (-a * |ξ|) * Real.exp (-(D.depth j + b) * |ξ|)) *
                        Real.cos (D.center j * ξ) := by rw [hexp]
              _ = Real.exp (-a * |ξ|) *
                    (D.weight j * Real.exp (-(D.depth j + b) * |ξ|) *
                      Real.cos (D.center j * ξ)) := by ring
      _ = ∑ j : Fin D.κ,
            (2 * Real.exp (-a * |ξ|)) *
              (D.weight j * Real.exp (-(D.depth j + b) * |ξ|) * Real.cos (D.center j * ξ)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = (2 * Real.exp (-a * |ξ|)) *
            ∑ j : Fin D.κ,
              D.weight j * Real.exp (-(D.depth j + b) * |ξ|) * Real.cos (D.center j * ξ) := by
            rw [Finset.mul_sum]
      _ = Real.exp (-a * |ξ|) *
            (2 * ∑ j : Fin D.κ,
              D.weight j * Real.exp (-(D.depth j + b) * |ξ|) * Real.cos (D.center j * ξ)) := by
            ring
      _ = xi_offline_neumann_cauchy_semigroup_generator_multiplier a ξ *
            D.xi_offline_neumann_cauchy_semigroup_generator_fourier_trace b ξ := by
            simp [xi_offline_neumann_cauchy_semigroup_generator_multiplier,
              xi_offline_neumann_cauchy_semigroup_generator_fourier_trace,
              xi_offline_neumann_cauchy_semigroup_generator_fourier_packet]
  · intro a x
    simp [xi_offline_neumann_cauchy_semigroup_generator_trace]
  · intro a ξ
    calc
      D.xi_offline_neumann_cauchy_semigroup_generator_fourier_derivative a ξ
          = 2 * ∑ j : Fin D.κ,
              -D.weight j * |ξ| * Real.exp (-(D.depth j + a) * |ξ|) *
                Real.cos (D.center j * ξ) := by
            rw [xi_offline_neumann_cauchy_semigroup_generator_fourier_derivative]
      _ = 2 * ∑ j : Fin D.κ,
            -|ξ| *
              (D.weight j * Real.exp (-(D.depth j + a) * |ξ|) * Real.cos (D.center j * ξ)) := by
            congr 1
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = ∑ j : Fin D.κ,
            (2 * -|ξ|) *
              (D.weight j * Real.exp (-(D.depth j + a) * |ξ|) * Real.cos (D.center j * ξ)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = (2 * -|ξ|) *
            ∑ j : Fin D.κ,
              D.weight j * Real.exp (-(D.depth j + a) * |ξ|) * Real.cos (D.center j * ξ) := by
            rw [Finset.mul_sum]
      _ = -|ξ| *
            (2 * ∑ j : Fin D.κ,
              D.weight j * Real.exp (-(D.depth j + a) * |ξ|) * Real.cos (D.center j * ξ)) := by
            ring
      _ = D.xi_offline_neumann_cauchy_semigroup_generator_half_laplacian a ξ := by
            simp [xi_offline_neumann_cauchy_semigroup_generator_half_laplacian,
              xi_offline_neumann_cauchy_semigroup_generator_fourier_trace,
              xi_offline_neumann_cauchy_semigroup_generator_fourier_packet]

end

end Omega.Zeta
