import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete quadratic datum for the continuous/discrete Legendre-Bregman quantization model. The
continuous contact point is `base + offset` with `offset ∈ [0, 1]`, so the two adjacent integers
`base` and `base + 1` are the only candidates for an optimal discrete quantizer. -/
structure ContinuousDiscreteLegendreBregmanData where
  base : ℤ
  offset : ℝ
  offset_nonneg : 0 ≤ offset
  offset_le_one : offset ≤ 1

namespace ContinuousDiscreteLegendreBregmanData

/-- Continuous contact point of the affine perturbation. -/
def contactPoint (D : ContinuousDiscreteLegendreBregmanData) : ℝ :=
  D.base + D.offset

/-- Strictly convex continuous objective. -/
def continuousObjective (D : ContinuousDiscreteLegendreBregmanData) (x : ℝ) : ℝ :=
  (x - D.contactPoint) ^ 2

/-- Discrete restriction of the objective to integers. -/
def discreteObjective (D : ContinuousDiscreteLegendreBregmanData) (k : ℤ) : ℝ :=
  D.continuousObjective k

/-- The quadratic Bregman gap from the contact point to an integer sample. -/
def bregmanGap (D : ContinuousDiscreteLegendreBregmanData) (k : ℤ) : ℝ :=
  (k - D.contactPoint) ^ 2

/-- Optimality among integer samples. -/
def optimalInteger (D : ContinuousDiscreteLegendreBregmanData) (k : ℤ) : Prop :=
  ∀ m : ℤ, D.discreteObjective k ≤ D.discreteObjective m

/-- The continuous-discrete gap is exactly the quadratic Bregman divergence. -/
def quantizationGapIdentity (D : ContinuousDiscreteLegendreBregmanData) : Prop :=
  ∀ k : ℤ, D.discreteObjective k = D.bregmanGap k

/-- Any optimal integer lies at one of the two adjacent integer contact points. -/
def nearestIntegerLocality (D : ContinuousDiscreteLegendreBregmanData) : Prop :=
  ∀ k : ℤ, D.optimalInteger k → k = D.base ∨ k = D.base + 1

/-- The optimal quantization gap is bounded by the quadratic Taylor remainder `1/4`. -/
def secondDerivativeGapBound (D : ContinuousDiscreteLegendreBregmanData) : Prop :=
  ∀ k : ℤ, D.optimalInteger k → D.discreteObjective k ≤ (1 : ℝ) / 4

end ContinuousDiscreteLegendreBregmanData

private lemma objective_at_base (D : ContinuousDiscreteLegendreBregmanData) :
    D.discreteObjective D.base = D.offset ^ 2 := by
  dsimp [ContinuousDiscreteLegendreBregmanData.discreteObjective,
    ContinuousDiscreteLegendreBregmanData.continuousObjective,
    ContinuousDiscreteLegendreBregmanData.contactPoint]
  ring_nf

private lemma objective_at_succ (D : ContinuousDiscreteLegendreBregmanData) :
    D.discreteObjective (D.base + 1) = (1 - D.offset) ^ 2 := by
  dsimp [ContinuousDiscreteLegendreBregmanData.discreteObjective,
    ContinuousDiscreteLegendreBregmanData.continuousObjective,
    ContinuousDiscreteLegendreBregmanData.contactPoint]
  norm_num

private lemma objective_base_lt_of_lt_base (D : ContinuousDiscreteLegendreBregmanData) {k : ℤ}
    (hk : k < D.base) : D.discreteObjective D.base < D.discreteObjective k := by
  have hk' : k ≤ D.base - 1 := by omega
  have hsq_lower : (1 + D.offset) ^ 2 ≤ D.discreteObjective k := by
    dsimp [ContinuousDiscreteLegendreBregmanData.discreteObjective,
      ContinuousDiscreteLegendreBregmanData.continuousObjective,
      ContinuousDiscreteLegendreBregmanData.contactPoint]
    have hsep : (k : ℝ) - ((D.base : ℝ) + D.offset) ≤ -(1 + D.offset) := by
      have hk_real : (k : ℝ) ≤ (D.base : ℝ) - 1 := by exact_mod_cast hk'
      nlinarith
    nlinarith [hsep, D.offset_nonneg]
  rw [objective_at_base D]
  nlinarith [hsq_lower, D.offset_nonneg]

private lemma objective_succ_lt_of_gt_succ (D : ContinuousDiscreteLegendreBregmanData)
    {k : ℤ} (hk : D.base + 1 < k) : D.discreteObjective (D.base + 1) < D.discreteObjective k := by
  have hk' : D.base + 2 ≤ k := by omega
  have hsq_lower : (2 - D.offset) ^ 2 ≤ D.discreteObjective k := by
    dsimp [ContinuousDiscreteLegendreBregmanData.discreteObjective,
      ContinuousDiscreteLegendreBregmanData.continuousObjective,
      ContinuousDiscreteLegendreBregmanData.contactPoint]
    have hsep : 2 - D.offset ≤ (k : ℝ) - ((D.base : ℝ) + D.offset) := by
      have hk_real : (D.base : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast hk'
      nlinarith
    have hnonneg : 0 ≤ 2 - D.offset := by linarith [D.offset_le_one]
    nlinarith [hsep, hnonneg]
  rw [objective_at_succ D]
  nlinarith [hsq_lower, D.offset_le_one]

private lemma nearest_integer_locality (D : ContinuousDiscreteLegendreBregmanData) (k : ℤ)
    (hopt : D.optimalInteger k) : k = D.base ∨ k = D.base + 1 := by
  by_cases hleft : k < D.base
  · exfalso
    have hcmp : D.discreteObjective k ≤ D.discreteObjective D.base := hopt D.base
    exact not_le_of_gt (objective_base_lt_of_lt_base D hleft) hcmp
  · by_cases hright : D.base + 1 < k
    · exfalso
      have hcmp : D.discreteObjective k ≤ D.discreteObjective (D.base + 1) := hopt (D.base + 1)
      exact not_le_of_gt (objective_succ_lt_of_gt_succ D hright) hcmp
    · have hk_bounds : D.base ≤ k ∧ k ≤ D.base + 1 := by
        constructor
        · exact le_of_not_gt hleft
        · exact le_of_not_gt hright
      omega

private lemma offset_le_half_of_optimal_base (D : ContinuousDiscreteLegendreBregmanData)
    (hopt : D.optimalInteger D.base) : D.offset ≤ (1 : ℝ) / 2 := by
  have hcmp : D.discreteObjective D.base ≤ D.discreteObjective (D.base + 1) := hopt (D.base + 1)
  rw [objective_at_base D, objective_at_succ D] at hcmp
  nlinarith [D.offset_nonneg, D.offset_le_one, hcmp]

private lemma half_le_offset_of_optimal_succ (D : ContinuousDiscreteLegendreBregmanData)
    (hopt : D.optimalInteger (D.base + 1)) : (1 : ℝ) / 2 ≤ D.offset := by
  have hcmp : D.discreteObjective (D.base + 1) ≤ D.discreteObjective D.base := hopt D.base
  rw [objective_at_succ D, objective_at_base D] at hcmp
  nlinarith [D.offset_nonneg, D.offset_le_one, hcmp]

/-- Paper label: `thm:conclusion-continuous-discrete-legendre-bregman-quantization`. For the
quadratic Legendre model centered at `base + offset`, the discrete gap is the Bregman divergence,
any optimal integer lies at the adjacent quantization sites `base` or `base + 1`, and the optimal
gap is bounded by the Taylor remainder `1/4`. -/
theorem paper_conclusion_continuous_discrete_legendre_bregman_quantization
    (D : ContinuousDiscreteLegendreBregmanData) :
    D.quantizationGapIdentity ∧ D.nearestIntegerLocality ∧ D.secondDerivativeGapBound := by
  refine ⟨?_, ?_, ?_⟩
  · intro k
    rfl
  · intro k hopt
    exact nearest_integer_locality D k hopt
  · intro k hopt
    rcases nearest_integer_locality D k hopt with hk | hk
    · subst hk
      rw [objective_at_base D]
      have hhalf : D.offset ≤ (1 : ℝ) / 2 := offset_le_half_of_optimal_base D hopt
      nlinarith [D.offset_nonneg, hhalf]
    · subst hk
      rw [objective_at_succ D]
      have hhalf : (1 : ℝ) / 2 ≤ D.offset := half_le_offset_of_optimal_succ D hopt
      nlinarith [D.offset_le_one, hhalf]

end Omega.Conclusion
