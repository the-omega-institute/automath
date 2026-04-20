import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- Poisson-smoothed cyclic Fourier profile. -/
noncomputable def xiPoissonSmoothedProfile {n : ℕ} (r : ℝ) (c : Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ :=
  fun k => r ^ (k : ℕ) * c k

/-- Cyclic Fourier projector deleting the zero mode. -/
def xiCyclicZeroProjector {n : ℕ} (u : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun k => if k = 0 then 0 else u k

/-- Quadratic reverse-KL proxy attached to a Jensen remainder. -/
noncomputable def xiReverseKLQuadraticRemainder {n : ℕ} (u v : Fin (n + 1) → ℝ) : ℝ :=
  ∑ k, (u k - v k) ^ 2

/-- Midpoint Jensen proxy between the lower and upper quadratic constants on `[a,b]`. -/
noncomputable def xiReverseKLJensenProxy {n : ℕ} (a b : ℝ) (u v : Fin (n + 1) → ℝ) : ℝ :=
  ((1 / (2 * b ^ 2) + 1 / (2 * a ^ 2)) / 2) * xiReverseKLQuadraticRemainder u v

/-- Energy carried by the deleted zero Fourier mode after Poisson smoothing. -/
noncomputable def xiDeletedZeroModeEnergy {n : ℕ} (r : ℝ) (c : Fin (n + 1) → ℝ) : ℝ :=
  (xiPoissonSmoothedProfile r c 0) ^ 2

private lemma xiReverseKLQuadraticRemainder_zero_projector {n : ℕ} (r : ℝ)
    (c : Fin (n + 1) → ℝ) :
    xiReverseKLQuadraticRemainder (xiPoissonSmoothedProfile r c)
        (xiCyclicZeroProjector (xiPoissonSmoothedProfile r c)) =
      xiDeletedZeroModeEnergy r c := by
  rw [xiReverseKLQuadraticRemainder, Fin.sum_univ_succ]
  simp [xiCyclicZeroProjector, xiDeletedZeroModeEnergy, xiPoissonSmoothedProfile]

/-- The quadratic Jensen proxy for the reverse-KL remainder is sandwiched between the endpoint
constants times the `L²` remainder, and for Poisson smoothing with the cyclic zero-mode projector
that remainder is exactly the deleted-mode energy.
    thm:xi-reversekl-cyclic-energy-equivalence -/
theorem paper_xi_reversekl_cyclic_energy_equivalence
    (n : ℕ) (a b r : ℝ) (ha : 0 < a) (hab : a ≤ b) (c : Fin (n + 1) → ℝ) :
    let p := xiPoissonSmoothedProfile r c
    let proj := xiCyclicZeroProjector p
    let E := xiDeletedZeroModeEnergy r c
    let J := xiReverseKLJensenProxy a b p proj
    (1 / (2 * b ^ 2)) * E ≤ J ∧
      J ≤ (1 / (2 * a ^ 2)) * E ∧
      0 ≤ E ∧
      xiReverseKLQuadraticRemainder p proj = E := by
  dsimp
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hCoeff :
      1 / (2 * b ^ 2) ≤ 1 / (2 * a ^ 2) := by
    have hMul : 2 * a ^ 2 ≤ 2 * b ^ 2 := by
      nlinarith [ha, hab]
    have hPosA : 0 < 2 * a ^ 2 := by positivity
    exact one_div_le_one_div_of_le hPosA hMul
  have hMidLower :
      1 / (2 * b ^ 2) ≤ (1 / (2 * b ^ 2) + 1 / (2 * a ^ 2)) / 2 := by
    nlinarith [hCoeff]
  have hMidUpper :
      (1 / (2 * b ^ 2) + 1 / (2 * a ^ 2)) / 2 ≤ 1 / (2 * a ^ 2) := by
    nlinarith [hCoeff]
  have hEnergyEq :
      xiReverseKLQuadraticRemainder (xiPoissonSmoothedProfile r c)
          (xiCyclicZeroProjector (xiPoissonSmoothedProfile r c)) =
        xiDeletedZeroModeEnergy r c :=
    xiReverseKLQuadraticRemainder_zero_projector r c
  have hEnergyNonneg : 0 ≤ xiDeletedZeroModeEnergy r c := by
    simpa [xiDeletedZeroModeEnergy] using sq_nonneg (xiPoissonSmoothedProfile r c 0)
  have hProxy :
      xiReverseKLJensenProxy a b (xiPoissonSmoothedProfile r c)
          (xiCyclicZeroProjector (xiPoissonSmoothedProfile r c)) =
        ((1 / (2 * b ^ 2) + 1 / (2 * a ^ 2)) / 2) * xiDeletedZeroModeEnergy r c := by
    simp [xiReverseKLJensenProxy, hEnergyEq]
  refine ⟨?_, ?_, hEnergyNonneg, hEnergyEq⟩
  · rw [hProxy]
    exact mul_le_mul_of_nonneg_right hMidLower hEnergyNonneg
  · rw [hProxy]
    exact mul_le_mul_of_nonneg_right hMidUpper hEnergyNonneg

end Omega.Zeta
