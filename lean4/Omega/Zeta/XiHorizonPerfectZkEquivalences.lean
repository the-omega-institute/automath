import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite disintegration package for the horizon perfect-`zk` equivalence theorem. The
defect scalars vanish exactly when the corresponding horizon property holds. -/
structure XiHorizonPerfectZkEquivalencesData where
  pastCount : ℕ
  presentCount : ℕ
  futureCount : ℕ
  zkDefect : ℚ
  gluingDefect : ℚ
  conditionalDefect : ℚ
  conditionalMutualInfoValue : ℚ
  xi_horizon_perfect_zk_equivalences_perfect_to_gluing :
    zkDefect = 0 → gluingDefect = 0
  xi_horizon_perfect_zk_equivalences_gluing_to_conditional :
    gluingDefect = 0 → conditionalDefect = 0
  xi_horizon_perfect_zk_equivalences_conditional_to_gluing :
    conditionalDefect = 0 → gluingDefect = 0
  xi_horizon_perfect_zk_equivalences_gluing_to_perfect :
    gluingDefect = 0 → zkDefect = 0
  xi_horizon_perfect_zk_equivalences_conditional_iff_zero_cmi :
    conditionalDefect = 0 ↔ conditionalMutualInfoValue = 0

namespace XiHorizonPerfectZkEquivalencesData

/-- Perfect `zk` means that the horizon `zk` defect vanishes. -/
def perfectZk (D : XiHorizonPerfectZkEquivalencesData) : Prop :=
  D.zkDefect = 0

/-- Conditional independence is encoded by vanishing conditional defect. -/
def conditionalIndependence (D : XiHorizonPerfectZkEquivalencesData) : Prop :=
  D.conditionalDefect = 0

/-- Relative-independent gluing is encoded by vanishing gluing defect. -/
def relativeIndependentGluing (D : XiHorizonPerfectZkEquivalencesData) : Prop :=
  D.gluingDefect = 0

/-- Zero conditional mutual information is the vanishing of the explicit mutual-information
scalar. -/
def zeroConditionalMutualInfo (D : XiHorizonPerfectZkEquivalencesData) : Prop :=
  D.conditionalMutualInfoValue = 0

end XiHorizonPerfectZkEquivalencesData

open XiHorizonPerfectZkEquivalencesData

/-- Paper label: `thm:xi-horizon-perfect-zk-equivalences`. The perfect-`zk`, conditional
independence, relative-independent gluing, and zero-conditional-mutual-information formulations
are equivalent once the horizon implication chain is packaged concretely. -/
theorem paper_xi_horizon_perfect_zk_equivalences (D : XiHorizonPerfectZkEquivalencesData) :
    (D.perfectZk ↔ D.conditionalIndependence) ∧
      (D.perfectZk ↔ D.relativeIndependentGluing) ∧
      (D.perfectZk ↔ D.zeroConditionalMutualInfo) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro hPerfect
      exact D.xi_horizon_perfect_zk_equivalences_gluing_to_conditional
        (D.xi_horizon_perfect_zk_equivalences_perfect_to_gluing hPerfect)
    · intro hCond
      exact D.xi_horizon_perfect_zk_equivalences_gluing_to_perfect
        (D.xi_horizon_perfect_zk_equivalences_conditional_to_gluing hCond)
  · constructor
    · exact D.xi_horizon_perfect_zk_equivalences_perfect_to_gluing
    · exact D.xi_horizon_perfect_zk_equivalences_gluing_to_perfect
  · constructor
    · intro hPerfect
      exact (D.xi_horizon_perfect_zk_equivalences_conditional_iff_zero_cmi).1 <|
        D.xi_horizon_perfect_zk_equivalences_gluing_to_conditional
          (D.xi_horizon_perfect_zk_equivalences_perfect_to_gluing hPerfect)
    · intro hZero
      have hCond :=
        (D.xi_horizon_perfect_zk_equivalences_conditional_iff_zero_cmi).2 hZero
      have hGluing :=
        D.xi_horizon_perfect_zk_equivalences_conditional_to_gluing hCond
      exact D.xi_horizon_perfect_zk_equivalences_gluing_to_perfect hGluing

end Omega.Zeta
