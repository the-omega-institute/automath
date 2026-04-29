import Mathlib.Tactic
import Omega.DerivedConsequences.DerivedZGSimplePoleDensityResidue
import Omega.Folding.FoldCollisionZeroReduction
import Omega.GU.BulkResonanceDeficit
import Omega.POM.CompleteHomogeneousPFInfty
import Omega.POM.FiberSymmetricOrderVisibleLayerSeparation

namespace Omega.DerivedConsequences

/-- Concrete derived package bundling a visible minimal-layer coincidence with a zero-reduction
threshold witness, and a bulk-resonance package combining PF∞ closure, the lower-density residue
identity, and the audited Fibonacci resonance deficit seeds. -/
def derived_visible_minimal_layer_threshold_failure_bulk_resonance_statement : Prop :=
  (Omega.POM.symmetricVisibleLayer [2, 2] = Omega.POM.symmetricVisibleLayer [2, 3] ∧
    Omega.POM.zigzagComponentLengthMultiset [2, 2] ≠
      Omega.POM.zigzagComponentLengthMultiset [2, 3] ∧
    Omega.Folding.foldMultiplicityCollisionProbability 0 ≤ 1) ∧
  (Omega.POM.IsPFInfinity (Omega.POM.completeHomogeneousSeq [1, 1]) ∧
    derived_zg_simple_pole_density_residue_statement ∧
    Nat.fib 8 = Nat.fib 7 + Nat.fib 6 ∧
    9 > 8)

/-- Paper label:
`thm:derived-visible-minimal-layer-threshold-failure-bulk-resonance`. -/
theorem paper_derived_visible_minimal_layer_threshold_failure_bulk_resonance :
    derived_visible_minimal_layer_threshold_failure_bulk_resonance_statement := by
  refine ⟨?_, ?_⟩
  · have hvisible :=
      Omega.POM.paper_pom_fiber_symmetric_order_visible_layer_separation
        [2, 2] [2, 3]
        (by
          intro n hn
          simp at hn
          omega)
        (by
          intro n hn
          simp at hn
          omega)
        rfl
        (by simp [Omega.POM.zigzagComponentLengthMultiset])
    have hzero :
        Omega.Folding.foldMultiplicityCollisionProbability 0 ≤ 1 := by
      simpa using Omega.Folding.paper_fold_collision_zero_reduction 0 0 1 rfl
    exact ⟨hvisible.1, hvisible.2.2.2, hzero⟩
  · have hpf :
      Omega.POM.IsPFInfinity (Omega.POM.completeHomogeneousSeq [1, 1]) :=
        Omega.POM.paper_pom_complete_homogeneous_pf_infty [1, 1]
    have hdensity := paper_derived_zg_simple_pole_density_residue
    rcases Omega.GU.paper_gut_cphi_forces_l2_tv_renyi2_deficit_seeds with
      ⟨_, hfib, _, _, hineq⟩
    exact ⟨hpf, hdensity, hfib, hineq.2.2⟩

end Omega.DerivedConsequences
