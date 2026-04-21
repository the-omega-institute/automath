import Omega.Zeta.AutomaticDirichletMoment

namespace Omega.Zeta

noncomputable section

/-- The critical logarithmic scale attached to the Dirichlet polynomial length. -/
def criticalScale (D : AutomaticDirichletMomentData) : ℝ :=
  Real.log (D.N : ℝ)

/-- The large-value threshold supplied by the power-saving exponent `ε`. -/
def criticalThreshold (D : AutomaticDirichletMomentData) (ε : ℝ) : ℝ :=
  (D.N : ℝ) ^ (-ε)

/-- The normalized large-values count bound obtained from the `2k`-th moment estimate. -/
def normalizedLargeValueBound (D : AutomaticDirichletMomentData) (k : ℕ) (T ε C : ℝ) : Prop :=
  D.momentValue k T / criticalThreshold D ε ≤
    C * T * (D.N : ℝ) ^ k * (criticalScale D) ^ (D.logExponent k)

/-- Critical-interval improvement package: the critical scale is positive and every moment bound
produces the corresponding normalized large-values estimate. -/
def CriticalIntervalStructureImprovement (D : AutomaticDirichletMomentData) : Prop :=
  0 < criticalScale D ∧
    ∀ k : ℕ, ∃ ε C, 0 < ε ∧ 0 < C ∧
      ∀ T : ℝ, 1 ≤ T → normalizedLargeValueBound D k T ε C

lemma criticalScale_pos (D : AutomaticDirichletMomentData) : 0 < criticalScale D := by
  unfold criticalScale
  have hN_real : (1 : ℝ) < D.N := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 1 < 2) D.hN
  exact Real.log_pos hN_real

/-- The conclusion69 uniform moment estimate immediately yields the critical-interval large-values
bound after dividing by the threshold factor `(N : ℝ)^(-ε)`.
    thm:conclusion70-critical-interval-structure-improvement -/
theorem paper_conclusion70_critical_interval_structure_improvement
    (D : AutomaticDirichletMomentData) : CriticalIntervalStructureImprovement D := by
  refine ⟨criticalScale_pos D, ?_⟩
  intro k
  rcases paper_conclusion69_automatic_dirichlet_moment D k with ⟨ε, C, hMoment⟩
  rcases hMoment with ⟨hε, hC, hBound⟩
  refine ⟨ε, C, hε, hC, ?_⟩
  intro T hT
  have hN_nat : 0 < D.N := lt_of_lt_of_le (by decide : 0 < 2) D.hN
  have hN_real : 0 < (D.N : ℝ) := by
    exact_mod_cast hN_nat
  have hThresholdPos : 0 < criticalThreshold D ε := by
    simpa [criticalThreshold] using Real.rpow_pos_of_pos hN_real (-ε)
  apply (_root_.div_le_iff₀ hThresholdPos).2
  simpa [AutomaticDirichletMomentData.uniformMomentBound, normalizedLargeValueBound,
    criticalThreshold, criticalScale, mul_assoc, mul_left_comm, mul_comm] using hBound T hT

end

end Omega.Zeta
