import Mathlib.Tactic
import Omega.Zeta.XiReverseKLCyclicEnergyEquivalence
import Omega.Zeta.XiReverseKLFourierGapPositiveKernelEnergy

open scoped BigOperators

namespace Omega.Zeta

/-- The Poisson-kernel lower endpoint `a_r = (1-r)/(1+r)`. -/
noncomputable def xiPoissonGapLowerScale (r : ℝ) : ℝ :=
  (1 - r) / (1 + r)

/-- The Poisson-kernel upper endpoint `b_r = (1+r)/(1-r)`. -/
noncomputable def xiPoissonGapUpperScale (r : ℝ) : ℝ :=
  (1 + r) / (1 - r)

/-- Finite-support Fourier-gap energy, normalized so the Jensen remainder takes the bilateral form
`a_r^2 S ≤ Δ ≤ b_r^2 S`. -/
noncomputable def xiPoissonFourierGap {n : ℕ} (r : ℝ) (c : Fin (n + 1) → ℝ) : ℝ :=
  xiDeletedZeroModeEnergy r c / 2

/-- Closed-form positive kernel for the finite-support Fourier gap. -/
noncomputable def xiPoissonGapKernel (r x : ℝ) : ℝ :=
  (r ^ 2 * (1 + r ^ 2) * (1 - Real.cos x)) /
    ((1 - r ^ 2) * (1 - 2 * r ^ 2 * Real.cos x + r ^ 4))

private lemma xiPoissonGapLower_pos (r : ℝ) (hr : 0 < r ∧ r < 1) :
    0 < xiPoissonGapLowerScale r := by
  dsimp [xiPoissonGapLowerScale]
  have hnum : 0 < 1 - r := by linarith
  have hden : 0 < 1 + r := by linarith
  exact div_pos hnum hden

private lemma xiPoissonGapLower_le_upper (r : ℝ) (hr : 0 < r ∧ r < 1) :
    xiPoissonGapLowerScale r ≤ xiPoissonGapUpperScale r := by
  have h1 : 0 < 1 + r := by linarith
  have h2 : 0 < 1 - r := by linarith
  have hlow : xiPoissonGapLowerScale r ≤ 1 := by
    dsimp [xiPoissonGapLowerScale]
    refine (div_le_iff₀ h1).2 ?_
    linarith
  have hupp : 1 ≤ xiPoissonGapUpperScale r := by
    dsimp [xiPoissonGapUpperScale]
    refine (le_div_iff₀ h2).2 ?_
    linarith
  exact le_trans hlow hupp

private lemma xiPoissonGapLower_sq_recip (r : ℝ) (hr : 0 < r ∧ r < 1) :
    xiPoissonGapLowerScale r ^ 2 = 1 / xiPoissonGapUpperScale r ^ 2 := by
  have h1 : 1 + r ≠ 0 := by linarith
  have h2 : 1 - r ≠ 0 := by linarith
  dsimp [xiPoissonGapLowerScale, xiPoissonGapUpperScale]
  field_simp [h1, h2]

private lemma xiPoissonGapUpper_sq_recip (r : ℝ) (hr : 0 < r ∧ r < 1) :
    xiPoissonGapUpperScale r ^ 2 = 1 / xiPoissonGapLowerScale r ^ 2 := by
  have h1 : 1 + r ≠ 0 := by linarith
  have h2 : 1 - r ≠ 0 := by linarith
  dsimp [xiPoissonGapLowerScale, xiPoissonGapUpperScale]
  field_simp [h1, h2]

/-- Paper label: `thm:xi-reversekl-poisson-gap-fourier-bilateral`. The finite-support reverse-KL
Jensen proxy is trapped between the Poisson endpoint scales times the normalized Fourier gap, and
the same chapter-local positive kernel gives a nonnegative Fourier-gap energy representation. -/
theorem paper_xi_reversekl_poisson_gap_fourier_bilateral (n : ℕ) (r : ℝ)
    (c : Fin (n + 1) → ℝ) (w : Fin (n + 1) → ℝ) (θ : Fin (n + 1) → ℝ) (hr : 0 < r ∧ r < 1)
    (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1) :
    xiPoissonGapLowerScale r ^ 2 * xiPoissonFourierGap r c ≤
        xiReverseKLJensenProxy (xiPoissonGapLowerScale r) (xiPoissonGapUpperScale r)
          (xiPoissonSmoothedProfile r c)
          (xiCyclicZeroProjector (xiPoissonSmoothedProfile r c)) ∧
      xiReverseKLJensenProxy (xiPoissonGapLowerScale r) (xiPoissonGapUpperScale r)
          (xiPoissonSmoothedProfile r c)
          (xiCyclicZeroProjector (xiPoissonSmoothedProfile r c)) ≤
        xiPoissonGapUpperScale r ^ 2 * xiPoissonFourierGap r c ∧
      0 ≤ xiPoissonFourierGap r c ∧
      0 ≤ ∑ i, ∑ j, w i * w j * xiPoissonGapKernel r (θ i - θ j) := by
  have ha : 0 < xiPoissonGapLowerScale r := xiPoissonGapLower_pos r hr
  have hab :
      xiPoissonGapLowerScale r ≤ xiPoissonGapUpperScale r := xiPoissonGapLower_le_upper r hr
  have hcyc :=
    paper_xi_reversekl_cyclic_energy_equivalence n (xiPoissonGapLowerScale r)
      (xiPoissonGapUpperScale r) r ha hab c
  have hkernel :=
    paper_xi_reversekl_fourier_gap_positive_kernel_energy n r w θ hr hw_nonneg hw_sum
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      xiPoissonGapLowerScale r ^ 2 * xiPoissonFourierGap r c
          = (1 / (2 * xiPoissonGapUpperScale r ^ 2)) * xiDeletedZeroModeEnergy r c := by
              rw [xiPoissonFourierGap, xiPoissonGapLower_sq_recip r hr]
              ring
      _ ≤ xiReverseKLJensenProxy (xiPoissonGapLowerScale r) (xiPoissonGapUpperScale r)
            (xiPoissonSmoothedProfile r c)
            (xiCyclicZeroProjector (xiPoissonSmoothedProfile r c)) := hcyc.1
  · calc
      xiReverseKLJensenProxy (xiPoissonGapLowerScale r) (xiPoissonGapUpperScale r)
          (xiPoissonSmoothedProfile r c)
          (xiCyclicZeroProjector (xiPoissonSmoothedProfile r c)) ≤
        (1 / (2 * xiPoissonGapLowerScale r ^ 2)) * xiDeletedZeroModeEnergy r c := hcyc.2.1
      _ = xiPoissonGapUpperScale r ^ 2 * xiPoissonFourierGap r c := by
            rw [xiPoissonFourierGap, xiPoissonGapUpper_sq_recip r hr]
            ring
  · have hnonneg : 0 ≤ xiDeletedZeroModeEnergy r c := hcyc.2.2.1
    have : 0 ≤ xiDeletedZeroModeEnergy r c / 2 := by nlinarith
    simpa [xiPoissonFourierGap] using this
  · simpa [xiPoissonGapKernel] using hkernel

end Omega.Zeta
