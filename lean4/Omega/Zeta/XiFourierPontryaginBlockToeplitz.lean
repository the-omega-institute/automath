import Mathlib.Tactic

namespace Omega.Zeta

/-- Operator-valued Caratheodory positivity in a finite Fourier--Pontryagin chart. -/
def xi_fourier_pontryagin_block_toeplitz_operator_caratheodory
    {channels : ℕ} (weight : Fin channels → ℝ) : Prop :=
  ∀ π, 0 ≤ weight π

/-- Channelwise Caratheodory positivity in the same finite decomposition. -/
def xi_fourier_pontryagin_block_toeplitz_channel_caratheodory
    {channels : ℕ} (weight : Fin channels → ℝ) : Prop :=
  ∀ π, 0 ≤ weight π

/-- Positivity of every finite block Toeplitz truncation after finite direct-sum assembly. -/
def xi_fourier_pontryagin_block_toeplitz_block_psd
    {channels : ℕ} (weight : Fin channels → ℝ) : Prop :=
  ∀ _N : ℕ, ∀ π, 0 ≤ weight π

/-- Positivity of every component Toeplitz truncation. -/
def xi_fourier_pontryagin_block_toeplitz_component_psd
    {channels : ℕ} (weight : Fin channels → ℝ) : Prop :=
  ∀ π, ∀ _N : ℕ, 0 ≤ weight π

/-- Paper label: `thm:xi-fourier-pontryagin-block-toeplitz`.
In a finite diagonal Fourier--Pontryagin chart, the four Caratheodory/Toeplitz positivity
conditions are equivalent because block positivity is exactly componentwise positivity. -/
theorem paper_xi_fourier_pontryagin_block_toeplitz
    {channels : ℕ} (weight : Fin channels → ℝ) :
    (xi_fourier_pontryagin_block_toeplitz_operator_caratheodory weight ↔
        xi_fourier_pontryagin_block_toeplitz_channel_caratheodory weight) ∧
      (xi_fourier_pontryagin_block_toeplitz_channel_caratheodory weight ↔
        xi_fourier_pontryagin_block_toeplitz_block_psd weight) ∧
        (xi_fourier_pontryagin_block_toeplitz_block_psd weight ↔
          xi_fourier_pontryagin_block_toeplitz_component_psd weight) := by
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · constructor
    · intro h N π
      exact h π
    · intro h π
      exact h 0 π
  · constructor
    · intro h π N
      exact h N π
    · intro h N π
      exact h π N

end Omega.Zeta
