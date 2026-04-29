import Omega.Conclusion.CriticalKernelSeparationCommonRecurrence
import Omega.Conclusion.MixedCollisionOverlapMultisetRigidity
import Omega.POM.MomentKernelExists
import Omega.POM.MomentMinrecurrenceHankel

namespace Omega.Conclusion

/-- Paper-facing finite-state package for mixed-collision rigidity: the compiled collision kernel
exists, the associated collision counts satisfy the Hankel-minimal recurrence, the overlap moments
recover the finite multiset of mixed overlaps, and any common-denominator presentation forces the
same recurrence coefficientwise. -/
def conclusion_mixed_collision_finite_state_mmd_recurrence_statement : Prop :=
  (∀ q : ℕ, 2 ≤ q →
    ∃ K : Omega.POM.MomentKernel q, ∀ m ≥ K.m0, K.count m = Omega.POM.momentCollisionCount q m) ∧
  (∀ q : ℕ, 2 ≤ q →
    ∃ d : ℕ, ∃ coeff : Fin d → ℚ, ∃ m0 : ℕ,
      Omega.POM.pom_moment_minrecurrence_hankel_recursWith q d m0 coeff ∧
        d = Omega.POM.hankel_rank_minimal_hankelRank
          (Omega.POM.pom_moment_minrecurrence_hankel_sequence q)) ∧
  (∀ {X : Type} [Fintype X] (w0 w1 : X → Rat),
    @mixedCollisionOverlapMultisetRigidity X _ w0 w1) ∧
  (∀ {α : Type*} (d : ℕ) (a : Fin d → ℚ) (seq N : α → ℕ → ℚ),
    criticalKernelGeneratingRelation d a seq N →
      criticalKernelNumeratorDegreeBound d N →
        ∀ x m, criticalKernelCommonRecurrence d a seq x m = 0)

theorem paper_conclusion_mixed_collision_finite_state_mmd_recurrence :
    conclusion_mixed_collision_finite_state_mmd_recurrence_statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q hq
    exact Omega.POM.paper_pom_moment_kernel_exists q hq
  · intro q hq
    exact Omega.POM.paper_pom_moment_minrecurrence_hankel q hq
  · intro X _ w0 w1
    exact @paper_conclusion_mixed_collision_overlap_multiset_rigidity X _ w0 w1
  · intro α d a seq N hrel hdeg x m
    exact paper_conclusion_critical_kernel_separation_common_recurrence d a seq N hrel hdeg x m

end Omega.Conclusion
