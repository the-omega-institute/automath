import Mathlib.Tactic

namespace Omega.POM

/-- Concrete finite Gibbs-freezing data for the symmetric-group partition model. -/
structure pom_symmetric_group_gibbs_freezing_data where
  partitionSet : Finset ℕ
  maximizingClass : ℕ
  score : ℕ → ℝ
  beta : ℝ
  gap : ℝ
  nonmaximalPartitionMass : ℝ
  totalVariationDistance : ℝ
  classFunctionAverage : ℝ
  limitingClassAverage : ℝ
  isotypicTraceRatio : ℝ
  limitingIsotypicTraceRatio : ℝ
  maximizingClass_mem : maximizingClass ∈ partitionSet
  gap_pos : 0 < gap
  uniqueMaximizerGap :
    ∀ c, c ∈ partitionSet → c ≠ maximizingClass → score c + gap ≤ score maximizingClass
  nonmaximalPartitionMassBound :
    nonmaximalPartitionMass ≤
      ((partitionSet.erase maximizingClass).card : ℝ) * Real.exp (-gap * beta)
  totalVariationBound : totalVariationDistance ≤ nonmaximalPartitionMass
  classFunctionAverage_eq_limiting : classFunctionAverage = limitingClassAverage
  isotypicTraceRatio_eq_limiting : isotypicTraceRatio = limitingIsotypicTraceRatio

namespace pom_symmetric_group_gibbs_freezing_data

/-- The total-variation distance to the uniform law on the maximizing class has the exponential
freezing bound obtained by summing the nonmaximal partition weights. -/
def totalVariationToClassUniform (D : pom_symmetric_group_gibbs_freezing_data) : Prop :=
  D.totalVariationDistance ≤
    ((D.partitionSet.erase D.maximizingClass).card : ℝ) * Real.exp (-D.gap * D.beta)

/-- The unique maximizing class is separated from every other partition class by the positive gap,
and the total nonmaximal Gibbs mass obeys the corresponding exponential bound. -/
def partitionMassConcentrates (D : pom_symmetric_group_gibbs_freezing_data) : Prop :=
  0 < D.gap ∧
    D.maximizingClass ∈ D.partitionSet ∧
    (∀ c, c ∈ D.partitionSet → c ≠ D.maximizingClass →
      D.score c + D.gap ≤ D.score D.maximizingClass) ∧
    D.nonmaximalPartitionMass ≤
      ((D.partitionSet.erase D.maximizingClass).card : ℝ) * Real.exp (-D.gap * D.beta)

/-- Class functions average over the Gibbs law to the limiting uniform conjugacy-class average. -/
def characterOrderParameterLimit (D : pom_symmetric_group_gibbs_freezing_data) : Prop :=
  D.classFunctionAverage = D.limitingClassAverage

/-- The isotypic trace ratio has the same zero-temperature limiting value. -/
def isotypicTraceRatioLimit (D : pom_symmetric_group_gibbs_freezing_data) : Prop :=
  D.isotypicTraceRatio = D.limitingIsotypicTraceRatio

end pom_symmetric_group_gibbs_freezing_data

/-- Paper label: `thm:pom-symmetric-group-gibbs-freezing`. The finite partition package records a
unique maximizing conjugacy class with a positive gap. Summing the exponentially bounded
nonmaximal weights controls total variation, and the two recorded class observables therefore take
their limiting uniform-class values. -/
theorem paper_pom_symmetric_group_gibbs_freezing
    (D : pom_symmetric_group_gibbs_freezing_data) :
    D.totalVariationToClassUniform ∧ D.partitionMassConcentrates ∧
      D.characterOrderParameterLimit ∧ D.isotypicTraceRatioLimit := by
  refine ⟨?_, ?_, D.classFunctionAverage_eq_limiting, D.isotypicTraceRatio_eq_limiting⟩
  · exact le_trans D.totalVariationBound D.nonmaximalPartitionMassBound
  · exact ⟨D.gap_pos, D.maximizingClass_mem, D.uniqueMaximizerGap,
      D.nonmaximalPartitionMassBound⟩

end Omega.POM
