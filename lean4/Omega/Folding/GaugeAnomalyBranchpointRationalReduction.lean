import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyDiscriminantFactorization

namespace Omega.Folding

/-- The linear-system solution for `X = t * u` obtained from the branchpoint equations. -/
def gaugeAnomalyBranchX (μ : ℚ) : ℚ :=
  μ ^ 2 * (3 * μ ^ 2 - 2 * μ - 1) / (μ ^ 2 + 1)

/-- The linear-system solution for `Y = u^3` obtained from the branchpoint equations. -/
def gaugeAnomalyBranchY (μ : ℚ) : ℚ :=
  -2 * μ * (μ ^ 2 - μ - 1) ^ 2 / (μ ^ 2 + 1)

/-- The `t = 2` rational reduction `u = R(μ) = X(μ) / 2`. -/
def gaugeAnomalyBranchR (μ : ℚ) : ℚ :=
  gaugeAnomalyBranchX μ / 2

/-- The explicit degree-10 elimination polynomial from the branchpoint duality certificate. -/
def gaugeAnomalyBranchQ10 (μ : ℚ) : ℚ :=
  27 * μ ^ 10 - 81 * μ ^ 9 + 90 * μ ^ 8 - 46 * μ ^ 7 + 11 * μ ^ 6 - μ ^ 5 -
    32 * μ ^ 4 + 32 * μ ^ 3 + 16 * μ + 16

/-- The explicit Tschirnhaus back-substitution polynomial `T(μ)`. -/
def gaugeAnomalyBranchTschirnhaus (μ : ℚ) : ℚ :=
  (-189 * μ ^ 9 + 540 * μ ^ 8 - 360 * μ ^ 7 - 308 * μ ^ 6 + 329 * μ ^ 5 +
      304 * μ ^ 4 - 104 * μ ^ 3 - 196 * μ ^ 2 - 128 * μ - 16) / 200

/-- The explicit `X(μ), Y(μ)` solve the two linear equations obtained from `F = 0` and
`∂_μ F = 0`. -/
def gaugeAnomalyBranchpointRationalReduction : Prop :=
  ∀ μ : ℚ,
    (μ ^ 4 - μ ^ 3 - μ ^ 2 - μ * gaugeAnomalyBranchY μ +
        (-μ ^ 2 + μ + 1) * gaugeAnomalyBranchX μ = 0) ∧
      (4 * μ ^ 3 - 3 * μ ^ 2 - 2 * μ - gaugeAnomalyBranchY μ +
        (1 - 2 * μ) * gaugeAnomalyBranchX μ = 0)

/-- At `t = 2`, the rational reduction recovers the resonant point `u = 1` at `μ = -1`, and that
special value is a zero of the quartic discriminant. -/
def gaugeAnomalyBranchpointSpecializationAtTwo : Prop :=
  gaugeAnomalyBranchX (-1) = 2 ∧
    gaugeAnomalyBranchY (-1) = 1 ∧
    gaugeAnomalyBranchR (-1) = 1 ∧
    gaugeAnomalyQuarticDiscriminant (gaugeAnomalyBranchR (-1)) = 0

/-- The rational reduction agrees with the explicit Tschirnhaus back-substitution modulo `Q10`. -/
def gaugeAnomalyBranchpointTschirnhausCongruence : Prop :=
  ∀ μ : ℚ,
    gaugeAnomalyBranchR μ - gaugeAnomalyBranchTschirnhaus μ =
      (7 * μ + 1) * gaugeAnomalyBranchQ10 μ / (200 * (μ ^ 2 + 1))

/-- Paper-facing wrapper for the branchpoint rational reduction: the explicit `X(μ), Y(μ)` solve
the branchpoint linear system, the `t = 2` specialization lands on `u = 1`, and the rational
reduction matches the degree-9 Tschirnhaus expression modulo `Q10`.
    prop:fold-gauge-anomaly-branchpoint-rational-reduction -/
theorem paper_fold_gauge_anomaly_branchpoint_rational_reduction :
    gaugeAnomalyBranchpointRationalReduction ∧
      gaugeAnomalyBranchpointSpecializationAtTwo ∧
      gaugeAnomalyBranchpointTschirnhausCongruence := by
  refine ⟨?_, ?_, ?_⟩
  · intro μ
    have hμ : μ ^ 2 + 1 ≠ 0 := by
      nlinarith [sq_nonneg μ]
    constructor
    · unfold gaugeAnomalyBranchX gaugeAnomalyBranchY
      field_simp [hμ]
      ring_nf
    · unfold gaugeAnomalyBranchX gaugeAnomalyBranchY
      field_simp [hμ]
      ring_nf
  · refine ⟨by norm_num [gaugeAnomalyBranchX], by norm_num [gaugeAnomalyBranchY], ?_, ?_⟩
    · norm_num [gaugeAnomalyBranchR, gaugeAnomalyBranchX]
    · norm_num [gaugeAnomalyBranchR, gaugeAnomalyBranchX, gaugeAnomalyQuarticDiscriminant]
  · intro μ
    have hμ : μ ^ 2 + 1 ≠ 0 := by
      nlinarith [sq_nonneg μ]
    unfold gaugeAnomalyBranchR gaugeAnomalyBranchX gaugeAnomalyBranchTschirnhaus
      gaugeAnomalyBranchQ10
    field_simp [hμ]
    ring_nf

end Omega.Folding
