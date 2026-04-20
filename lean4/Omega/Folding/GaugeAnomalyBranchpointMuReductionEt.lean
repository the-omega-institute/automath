import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyBranchpointRationalReduction

namespace Omega.Folding

/-- The branchpoint elimination polynomial obtained after clearing denominators from
`u = X(μ) / t` and `u^3 = Y(μ)`. -/
def gaugeAnomalyEt (t μ : ℚ) : ℚ :=
  2 * t ^ 3 * (μ ^ 2 + 1) ^ 2 * (μ ^ 2 - μ - 1) ^ 2 + μ ^ 5 * (3 * μ ^ 2 - 2 * μ - 1) ^ 3

/-- Rational recovery of `u` from the branchpoint parameter `μ`. -/
def gaugeAnomalyRecoveredU (t μ : ℚ) : ℚ :=
  gaugeAnomalyBranchX μ / t

/-- The quartic branch polynomial from the paper. -/
def gaugeAnomalyFt (t μ u : ℚ) : ℚ :=
  μ ^ 4 - μ ^ 3 - (t * u + 1) * μ ^ 2 + μ * (t * u - u ^ 3) + t * u

/-- The derivative of `F_t(μ,u)` in the `μ` variable. -/
def gaugeAnomalyFtDerivMu (t μ u : ℚ) : ℚ :=
  4 * μ ^ 3 - 3 * μ ^ 2 - 2 * μ - u ^ 3 + (1 - 2 * μ) * (t * u)

/-- The single polynomial criterion equivalent to the cubic consistency relation
`(X(μ) / t)^3 = Y(μ)` once `μ ≠ 0`. -/
def gaugeAnomalyEtBranchpointCriterion : Prop :=
  ∀ t μ : ℚ, t ≠ 0 → μ ≠ 0 →
    (gaugeAnomalyEt t μ = 0 ↔ gaugeAnomalyRecoveredU t μ ^ 3 = gaugeAnomalyBranchY μ)

/-- Vanishing of `E_t(μ)` recovers a genuine branchpoint pair for the quartic. -/
def gaugeAnomalyEtRationalRecovery : Prop :=
  ∀ t μ : ℚ, t ≠ 0 → μ ≠ 0 → gaugeAnomalyEt t μ = 0 →
    let u := gaugeAnomalyRecoveredU t μ
    gaugeAnomalyFt t μ u = 0 ∧ gaugeAnomalyFtDerivMu t μ u = 0

/-- At `t = 2`, the elimination polynomial factors through the audited degree-10 branch factor,
and `μ = -1` recovers the resonant point `u = 1`. -/
def gaugeAnomalyEtSpecializationAtTwo : Prop :=
  (∀ μ : ℚ, gaugeAnomalyEt 2 μ = (μ + 1) * gaugeAnomalyBranchQ10 μ) ∧
    gaugeAnomalyRecoveredU 2 (-1) = 1

private lemma gaugeAnomalyRecoveredU_sub_branchY (t μ : ℚ) (ht : t ≠ 0) :
    gaugeAnomalyRecoveredU t μ ^ 3 - gaugeAnomalyBranchY μ =
      μ * gaugeAnomalyEt t μ / (t ^ 3 * (μ ^ 2 + 1) ^ 3) := by
  have hμ : μ ^ 2 + 1 ≠ 0 := by
    nlinarith [sq_nonneg μ]
  unfold gaugeAnomalyRecoveredU gaugeAnomalyEt gaugeAnomalyBranchX gaugeAnomalyBranchY
  field_simp [ht, hμ]
  ring

private theorem gaugeAnomalyEtCriterion_iff (t μ : ℚ) (ht : t ≠ 0) (hμ : μ ≠ 0) :
    gaugeAnomalyEt t μ = 0 ↔ gaugeAnomalyRecoveredU t μ ^ 3 = gaugeAnomalyBranchY μ := by
  have hμ1 : μ ^ 2 + 1 ≠ 0 := by
    nlinarith [sq_nonneg μ]
  have hden : t ^ 3 * (μ ^ 2 + 1) ^ 3 ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero 3 ht) (pow_ne_zero 3 hμ1)
  constructor
  · intro hEt
    have hsub :
        gaugeAnomalyRecoveredU t μ ^ 3 - gaugeAnomalyBranchY μ = 0 := by
      rw [gaugeAnomalyRecoveredU_sub_branchY t μ ht, hEt, mul_zero, zero_div]
    exact sub_eq_zero.mp hsub
  · intro hEq
    have hsub :
        gaugeAnomalyRecoveredU t μ ^ 3 - gaugeAnomalyBranchY μ = 0 := sub_eq_zero.mpr hEq
    rw [gaugeAnomalyRecoveredU_sub_branchY t μ ht] at hsub
    have hmul : μ * gaugeAnomalyEt t μ = 0 := by
      exact ((div_eq_zero_iff).mp hsub).resolve_right hden
    exact (mul_eq_zero.mp hmul).resolve_left hμ

private theorem gaugeAnomalyEtCriterion_proof : gaugeAnomalyEtBranchpointCriterion := by
  unfold gaugeAnomalyEtBranchpointCriterion
  exact fun t μ ht hμ => gaugeAnomalyEtCriterion_iff t μ ht hμ

/-- Paper-facing package for the `E_t(μ)` reduction.
    prop:fold-gauge-anomaly-branchpoint-mu-reduction-Et -/
theorem paper_fold_gauge_anomaly_branchpoint_mu_reduction_et :
    gaugeAnomalyEtBranchpointCriterion ∧
    gaugeAnomalyEtRationalRecovery ∧
      gaugeAnomalyEtSpecializationAtTwo := by
  refine ⟨?_, ?_, ?_⟩
  · exact gaugeAnomalyEtCriterion_proof
  · intro t μ ht hμ hEt
    dsimp
    have hCube :
        gaugeAnomalyRecoveredU t μ ^ 3 = gaugeAnomalyBranchY μ :=
      (gaugeAnomalyEtCriterion_iff t μ ht hμ).mp hEt
    have hSystem := (paper_fold_gauge_anomaly_branchpoint_rational_reduction).1 μ
    constructor
    · unfold gaugeAnomalyFt
      have htu : t * gaugeAnomalyRecoveredU t μ = gaugeAnomalyBranchX μ := by
        unfold gaugeAnomalyRecoveredU
        field_simp [ht]
      have h0 := hSystem.1
      rw [htu, hCube]
      ring_nf at h0 ⊢
      exact h0
    · unfold gaugeAnomalyFtDerivMu
      have htu : t * gaugeAnomalyRecoveredU t μ = gaugeAnomalyBranchX μ := by
        unfold gaugeAnomalyRecoveredU
        field_simp [ht]
      have h0 := hSystem.2
      rw [htu, hCube]
      ring_nf at h0 ⊢
      exact h0
  · refine ⟨?_, ?_⟩
    · intro μ
      unfold gaugeAnomalyEt gaugeAnomalyBranchQ10
      ring
    · norm_num [gaugeAnomalyRecoveredU, gaugeAnomalyBranchX]

end Omega.Folding
