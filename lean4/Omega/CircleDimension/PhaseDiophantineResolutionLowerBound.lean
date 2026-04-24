import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Phase-decoding injectivity at tolerance `ε` forces the tolerance below half of the minimal
phase separation `δ`. -/
def phaseResolutionInjective (ε δ : ℝ) : Prop :=
  ε < δ / 2

/-- The discrete external register scale attached to the next convergent denominator. -/
def externalRegisterCutoff (qNext : ℕ) : ℕ :=
  qNext

/-- Paper-facing Diophantine phase-resolution bound: once the continued-fraction denominator
`q_{j+1}` controls the minimal separation up to radius `2N`, any injective phase decoder must work
below the `1 / (2 q_{j+1})` scale, and the corresponding external register cutoff is at least
`q_{j+1}`. -/
theorem paper_cdim_phase_diophantine_resolution_lower_bound
    (N qj qj1 : ℕ) (δ2N ε : ℝ)
    (hNpos : 0 < N)
    (hqj : qj ≤ 2 * N)
    (hnext : 2 * N < qj1)
    (hδlower : (1 : ℝ) / ((qj1 : ℝ) + qj) < δ2N)
    (hδupper : δ2N ≤ (1 : ℝ) / qj1)
    (hinj : phaseResolutionInjective ε δ2N) :
    (1 : ℝ) / ((qj1 : ℝ) + qj) < δ2N ∧
      ε < (1 : ℝ) / (2 * qj1) ∧
      (1 : ℝ) / (2 * qj1) ≤ (1 : ℝ) / (2 * N) ∧
      2 * N < externalRegisterCutoff qj1 := by
  have hqj1_nat_pos : 0 < qj1 := by
    omega
  have hqj1_pos : 0 < (qj1 : ℝ) := by
    exact_mod_cast hqj1_nat_pos
  have h2N_pos : 0 < (2 * N : ℝ) := by
    positivity
  have hε : ε < δ2N / 2 := by
    simpa [phaseResolutionInjective] using hinj
  have hhalf : δ2N / 2 ≤ (1 : ℝ) / (2 * qj1) := by
    have htmp : δ2N / 2 ≤ ((1 : ℝ) / qj1) / 2 := by
      exact div_le_div_of_nonneg_right hδupper (by positivity)
    have hrewrite : ((1 : ℝ) / qj1) / 2 = (1 : ℝ) / (2 * qj1) := by
      field_simp [hqj1_pos.ne']
    simpa [hrewrite] using htmp
  have hregisterBound : (1 : ℝ) / (2 * qj1) ≤ (1 : ℝ) / (2 * N) := by
    have hle_nat : 2 * N ≤ 2 * qj1 := by
      omega
    have hle : (2 * N : ℝ) ≤ (2 * qj1 : ℝ) := by
      exact_mod_cast hle_nat
    exact one_div_le_one_div_of_le h2N_pos hle
  refine ⟨hδlower, lt_of_lt_of_le hε hhalf, hregisterBound, ?_⟩
  simpa [externalRegisterCutoff] using hnext

end Omega.CircleDimension
