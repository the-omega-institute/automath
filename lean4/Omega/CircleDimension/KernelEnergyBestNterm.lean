import Omega.CircleDimension.KernelEnergyLaguerreParseval

namespace Omega.CircleDimension

open scoped BigOperators

noncomputable section

/-- The orthogonal truncation keeping exactly the first `K` Laguerre coordinates. -/
def cdimLaguerreProjection {N : ℕ} (K : ℕ) (coord : Fin N → ℂ) : Fin N → ℂ :=
  fun n ↦ if n.1 < K then coord n else 0

/-- A coordinate vector is `K`-bandlimited when every index `n ≥ K` vanishes. -/
def cdimLaguerreBandlimited {N : ℕ} (K : ℕ) (coord : Fin N → ℂ) : Prop :=
  ∀ n, K ≤ n.1 → coord n = 0

/-- Generic weighted Laguerre energy. -/
def cdimLaguerreEnergy {N : ℕ} (coord : Fin N → ℂ) : ℝ :=
  ∑ n, cdimLaguerreWeight n * ‖coord n‖ ^ 2

/-- Generic `K`-term Laguerre truncation energy. -/
def cdimLaguerreTruncation {N : ℕ} (K : ℕ) (coord : Fin N → ℂ) : ℝ :=
  ∑ n, if n.1 < K then cdimLaguerreWeight n * ‖coord n‖ ^ 2 else 0

/-- Tail energy beyond the first `K` Laguerre coordinates. -/
def cdimLaguerreTailEnergy {N : ℕ} (K : ℕ) (coord : Fin N → ℂ) : ℝ :=
  ∑ n, if K ≤ n.1 then cdimLaguerreWeight n * ‖coord n‖ ^ 2 else 0

/-- Head contribution of a `K`-bandlimited approximation error. -/
def cdimLaguerreHeadError {N : ℕ} (K : ℕ) (coord approx : Fin N → ℂ) : ℝ :=
  ∑ n, if n.1 < K then cdimLaguerreWeight n * ‖coord n - approx n‖ ^ 2 else 0

/-- Weighted approximation error in Laguerre coordinates. -/
def cdimLaguerreError {N : ℕ} (coord approx : Fin N → ℂ) : ℝ :=
  ∑ n, cdimLaguerreWeight n * ‖coord n - approx n‖ ^ 2

/-- Simultaneous `K`-bandlimitedness on the positive and negative halves. -/
def cdimKernelBandlimited {N : ℕ} (K : ℕ) (pos neg : Fin N → ℂ) : Prop :=
  cdimLaguerreBandlimited K pos ∧ cdimLaguerreBandlimited K neg

/-- Kernel-energy approximation error after splitting into positive and negative Laguerre halves. -/
def cdimKernelApproxError {N : ℕ} (pos neg posApprox negApprox : Fin N → ℂ) : ℝ :=
  cdimLaguerreError pos posApprox + cdimLaguerreError neg negApprox

lemma cdimLaguerreProjection_bandlimited {N : ℕ} (K : ℕ) (coord : Fin N → ℂ) :
    cdimLaguerreBandlimited K (cdimLaguerreProjection K coord) := by
  intro n hn
  simp [cdimLaguerreProjection, Nat.not_lt_of_ge hn]

lemma cdimLaguerreEnergy_eq_truncation_add_tail {N : ℕ} (K : ℕ) (coord : Fin N → ℂ) :
    cdimLaguerreEnergy coord = cdimLaguerreTruncation K coord + cdimLaguerreTailEnergy K coord := by
  unfold cdimLaguerreEnergy cdimLaguerreTruncation cdimLaguerreTailEnergy
  calc
    ∑ n, cdimLaguerreWeight n * ‖coord n‖ ^ 2 =
        ∑ n,
          ((if n.1 < K then cdimLaguerreWeight n * ‖coord n‖ ^ 2 else 0) +
            (if K ≤ n.1 then cdimLaguerreWeight n * ‖coord n‖ ^ 2 else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro n _
          by_cases hlt : n.1 < K
          · simp [hlt, Nat.not_le.mpr hlt]
          · have hge : K ≤ n.1 := Nat.le_of_not_gt hlt
            simp [hlt, hge]
    _ = cdimLaguerreTruncation K coord + cdimLaguerreTailEnergy K coord := by
      simp [cdimLaguerreTruncation, cdimLaguerreTailEnergy, Finset.sum_add_distrib]

lemma cdimLaguerreError_split {N : ℕ} (K : ℕ) (coord approx : Fin N → ℂ)
    (happrox : cdimLaguerreBandlimited K approx) :
    cdimLaguerreError coord approx =
      cdimLaguerreHeadError K coord approx + cdimLaguerreTailEnergy K coord := by
  unfold cdimLaguerreError cdimLaguerreHeadError cdimLaguerreTailEnergy
  calc
    ∑ n, cdimLaguerreWeight n * ‖coord n - approx n‖ ^ 2 =
        ∑ n,
          ((if n.1 < K then cdimLaguerreWeight n * ‖coord n - approx n‖ ^ 2 else 0) +
            (if K ≤ n.1 then cdimLaguerreWeight n * ‖coord n‖ ^ 2 else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro n _
          by_cases hlt : n.1 < K
          · simp [hlt, Nat.not_le.mpr hlt]
          · have hge : K ≤ n.1 := Nat.le_of_not_gt hlt
            simp [hlt, hge, happrox n hge]
    _ = cdimLaguerreHeadError K coord approx + cdimLaguerreTailEnergy K coord := by
      simp [cdimLaguerreHeadError, cdimLaguerreTailEnergy, Finset.sum_add_distrib]

lemma cdimLaguerreTruncation_eq_positive {N : ℕ} (K : ℕ) (coord : Fin N → ℂ) :
    cdimLaguerreTruncation K coord = cdimPositiveLaguerreTruncation K coord := by
  classical
  unfold cdimLaguerreTruncation cdimPositiveLaguerreTruncation
  symm
  exact Finset.sum_filter (fun n : Fin N ↦ n.1 < K)
    (fun n ↦ cdimLaguerreWeight n * ‖coord n‖ ^ 2)

lemma cdimLaguerreTruncation_eq_negative {N : ℕ} (K : ℕ) (coord : Fin N → ℂ) :
    cdimLaguerreTruncation K coord = cdimNegativeLaguerreTruncation K coord := by
  classical
  unfold cdimLaguerreTruncation cdimNegativeLaguerreTruncation
  symm
  exact Finset.sum_filter (fun n : Fin N ↦ n.1 < K)
    (fun n ↦ cdimLaguerreWeight n * ‖coord n‖ ^ 2)

lemma cdimLaguerreHeadError_nonneg {N : ℕ} (K : ℕ) (coord approx : Fin N → ℂ) :
    0 ≤ cdimLaguerreHeadError K coord approx := by
  unfold cdimLaguerreHeadError
  refine Finset.sum_nonneg ?_
  intro n _
  by_cases hlt : n.1 < K
  · have hweight : 0 ≤ cdimLaguerreWeight n := by
      unfold cdimLaguerreWeight
      positivity
    simp [hlt]
    positivity
  · simp [hlt]

lemma cdimLaguerreError_projection_eq_tail {N : ℕ} (K : ℕ) (coord : Fin N → ℂ) :
    cdimLaguerreError coord (cdimLaguerreProjection K coord) = cdimLaguerreTailEnergy K coord := by
  have hsplit :=
    cdimLaguerreError_split K coord (cdimLaguerreProjection K coord)
      (cdimLaguerreProjection_bandlimited K coord)
  have hhead : cdimLaguerreHeadError K coord (cdimLaguerreProjection K coord) = 0 := by
    unfold cdimLaguerreHeadError cdimLaguerreProjection
    refine Finset.sum_eq_zero ?_
    intro n _
    by_cases hlt : n.1 < K
    · simp [hlt]
    · simp [hlt]
  linarith

lemma cdimLaguerreTailEnergy_le_error {N : ℕ} (K : ℕ) (coord approx : Fin N → ℂ)
    (happrox : cdimLaguerreBandlimited K approx) :
    cdimLaguerreTailEnergy K coord ≤ cdimLaguerreError coord approx := by
  have hsplit := cdimLaguerreError_split K coord approx happrox
  have hnonneg : 0 ≤ cdimLaguerreHeadError K coord approx :=
    cdimLaguerreHeadError_nonneg K coord approx
  linarith

/-- Concrete best-`N`-term statement for the finite Laguerre-coordinate model of kernel energy. -/
def cdimKernelEnergyBestNtermStatement : Prop :=
  ∀ {N : ℕ} (K : ℕ) (pos neg : Fin N → ℂ),
    let posN := cdimLaguerreProjection K pos
    let negN := cdimLaguerreProjection K neg
    cdimKernelBandlimited K posN negN ∧
      cdimKernelApproxError pos neg posN negN =
        cdimKernelEnergyForm pos neg -
          (cdimPositiveLaguerreTruncation K pos + cdimNegativeLaguerreTruncation K neg) ∧
      ∀ pos' neg', cdimKernelBandlimited K pos' neg' →
        cdimKernelApproxError pos neg posN negN ≤ cdimKernelApproxError pos neg pos' neg'

set_option maxHeartbeats 400000 in
/-- Paper label: `prop:cdim-kernel-energy-best-nterm`. -/
theorem paper_cdim_kernel_energy_best_nterm :
    cdimKernelEnergyBestNtermStatement := by
  intro N K pos neg
  let posN := cdimLaguerreProjection K pos
  let negN := cdimLaguerreProjection K neg
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨cdimLaguerreProjection_bandlimited K pos, cdimLaguerreProjection_bandlimited K neg⟩
  · have hposErr : cdimLaguerreError pos posN = cdimLaguerreTailEnergy K pos := by
      simpa [posN] using cdimLaguerreError_projection_eq_tail K pos
    have hnegErr : cdimLaguerreError neg negN = cdimLaguerreTailEnergy K neg := by
      simpa [negN] using cdimLaguerreError_projection_eq_tail K neg
    have hposDecomp :
        cdimPositiveLaguerreEnergy pos =
          cdimPositiveLaguerreTruncation K pos + cdimLaguerreTailEnergy K pos := by
      rw [← cdimLaguerreTruncation_eq_positive K pos]
      simpa [cdimLaguerreEnergy, cdimPositiveLaguerreEnergy] using
        cdimLaguerreEnergy_eq_truncation_add_tail K pos
    have hnegDecomp :
        cdimNegativeLaguerreEnergy neg =
          cdimNegativeLaguerreTruncation K neg + cdimLaguerreTailEnergy K neg := by
      rw [← cdimLaguerreTruncation_eq_negative K neg]
      simpa [cdimLaguerreEnergy, cdimNegativeLaguerreEnergy] using
        cdimLaguerreEnergy_eq_truncation_add_tail K neg
    unfold cdimKernelApproxError cdimKernelEnergyForm
    linarith
  · intro pos' neg' hband
    have hposLower := cdimLaguerreTailEnergy_le_error K pos pos' hband.1
    have hnegLower := cdimLaguerreTailEnergy_le_error K neg neg' hband.2
    have hproj :
        cdimKernelApproxError pos neg posN negN =
          cdimLaguerreTailEnergy K pos + cdimLaguerreTailEnergy K neg := by
      unfold cdimKernelApproxError
      rw [show cdimLaguerreError pos posN = cdimLaguerreTailEnergy K pos by
        simpa [posN] using cdimLaguerreError_projection_eq_tail K pos]
      rw [show cdimLaguerreError neg negN = cdimLaguerreTailEnergy K neg by
        simpa [negN] using cdimLaguerreError_projection_eq_tail K neg]
    unfold cdimKernelApproxError at *
    linarith

end

end Omega.CircleDimension
