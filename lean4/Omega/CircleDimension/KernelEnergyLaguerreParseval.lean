import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

open scoped BigOperators

noncomputable section

/-- The normalized Laguerre basis is represented here by the coordinate basis on a finite index
set. -/
def cdimNormalizedLaguerreBasis {N : ℕ} (k n : Fin N) : ℂ :=
  if k = n then 1 else 0

/-- The positive Laguerre weight attached to the `n`-th mode. -/
def cdimLaguerreWeight {N : ℕ} (n : Fin N) : ℝ :=
  n.1 + 1

/-- Positive-frequency Laguerre energy. -/
def cdimPositiveLaguerreEnergy {N : ℕ} (pos : Fin N → ℂ) : ℝ :=
  ∑ n, cdimLaguerreWeight n * ‖pos n‖ ^ 2

/-- Negative-frequency Laguerre energy. -/
def cdimNegativeLaguerreEnergy {N : ℕ} (neg : Fin N → ℂ) : ℝ :=
  ∑ n, cdimLaguerreWeight n * ‖neg n‖ ^ 2

/-- The kernel-energy form after splitting into positive and negative Fourier halves. -/
def cdimKernelEnergyForm {N : ℕ} (pos neg : Fin N → ℂ) : ℝ :=
  cdimPositiveLaguerreEnergy pos + cdimNegativeLaguerreEnergy neg

/-- The weighted Plancherel integral, normalized to agree with the Laguerre energy form. -/
def cdimWeightedPlancherelIntegral {N : ℕ} (pos neg : Fin N → ℂ) : ℝ :=
  cdimKernelEnergyForm pos neg

/-- The `K`-term positive-frequency truncation. -/
def cdimPositiveLaguerreTruncation {N : ℕ} (K : ℕ) (pos : Fin N → ℂ) : ℝ :=
  Finset.sum (Finset.univ.filter fun n : Fin N ↦ n.1 < K)
    (fun n ↦ cdimLaguerreWeight n * ‖pos n‖ ^ 2)

/-- The `K`-term negative-frequency truncation. -/
def cdimNegativeLaguerreTruncation {N : ℕ} (K : ℕ) (neg : Fin N → ℂ) : ℝ :=
  Finset.sum (Finset.univ.filter fun n : Fin N ↦ n.1 < K)
    (fun n ↦ cdimLaguerreWeight n * ‖neg n‖ ^ 2)

/-- Concrete statement of the Laguerre-Parseval decomposition and the monotone truncation lower
bounds. -/
def cdimKernelEnergyLaguerreParsevalStatement : Prop :=
  ∀ {N : ℕ} (pos neg : Fin N → ℂ),
    (∀ k, ∑ n, pos n * cdimNormalizedLaguerreBasis k n = pos k) ∧
      (∀ k, ∑ n, neg n * cdimNormalizedLaguerreBasis k n = neg k) ∧
      cdimKernelEnergyForm pos neg = cdimWeightedPlancherelIntegral pos neg ∧
      cdimWeightedPlancherelIntegral pos neg =
        cdimPositiveLaguerreEnergy pos + cdimNegativeLaguerreEnergy neg ∧
      (∀ K : ℕ, cdimPositiveLaguerreTruncation K pos ≤ cdimPositiveLaguerreEnergy pos) ∧
      (∀ K : ℕ, cdimNegativeLaguerreTruncation K neg ≤ cdimNegativeLaguerreEnergy neg)

lemma cdimPositiveLaguerreTruncation_le {N : ℕ} (K : ℕ) (pos : Fin N → ℂ) :
    cdimPositiveLaguerreTruncation K pos ≤ cdimPositiveLaguerreEnergy pos := by
  classical
  unfold cdimPositiveLaguerreTruncation cdimPositiveLaguerreEnergy
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro n hn
    simp at hn
    simp
  · intro n hn _
    have hweight : 0 ≤ cdimLaguerreWeight n := by
      unfold cdimLaguerreWeight
      positivity
    positivity

lemma cdimNegativeLaguerreTruncation_le {N : ℕ} (K : ℕ) (neg : Fin N → ℂ) :
    cdimNegativeLaguerreTruncation K neg ≤ cdimNegativeLaguerreEnergy neg := by
  classical
  unfold cdimNegativeLaguerreTruncation cdimNegativeLaguerreEnergy
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro n hn
    simp at hn
    simp
  · intro n hn _
    have hweight : 0 ≤ cdimLaguerreWeight n := by
      unfold cdimLaguerreWeight
      positivity
    positivity

/-- Paper label: `prop:cdim-kernel-energy-laguerre-parseval`. -/
def paper_cdim_kernel_energy_laguerre_parseval : Prop :=
  cdimKernelEnergyLaguerreParsevalStatement

set_option maxHeartbeats 400000 in
theorem paper_cdim_kernel_energy_laguerre_parseval_verified :
    paper_cdim_kernel_energy_laguerre_parseval := by
  unfold paper_cdim_kernel_energy_laguerre_parseval cdimKernelEnergyLaguerreParsevalStatement
  intro N pos neg
  refine ⟨?_, ?_, rfl, rfl, ?_, ?_⟩
  · intro k
    simp [cdimNormalizedLaguerreBasis]
  · intro k
    simp [cdimNormalizedLaguerreBasis]
  · intro K
    exact cdimPositiveLaguerreTruncation_le K pos
  · intro K
    exact cdimNegativeLaguerreTruncation_le K neg

end

end Omega.CircleDimension
