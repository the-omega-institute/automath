import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete bulk/code/boundary data for the holographic sufficient-statistic statement. External
observables are evaluated on the embedded code subspace, and every such observable comes with a
boundary reconstruction rule. -/
structure DephysHolographySufficientStatisticData where
  Bulk : Type
  Code : Type
  Boundary : Type
  Obs : Type
  Value : Type
  codeEmbedding : Code → Bulk
  boundaryEncode : Code → Boundary
  externalObservable : Obs → Bulk → Value
  boundaryReconstruction : Obs → Boundary → Value
  paper_label_dephys_holography_sufficient_statistic_reconstruction :
    ∀ O : Obs, ∀ c : Code,
      externalObservable O (codeEmbedding c) =
        boundaryReconstruction O (boundaryEncode c)

namespace DephysHolographySufficientStatisticData

def codePrediction (D : DephysHolographySufficientStatisticData) (O : D.Obs) : D.Code → D.Value :=
  fun c => D.externalObservable O (D.codeEmbedding c)

def boundaryPrediction (D : DephysHolographySufficientStatisticData) (O : D.Obs) :
    D.Boundary → D.Value :=
  D.boundaryReconstruction O

/-- Boundary sufficiency on the code subspace means that every external observable factors through
the boundary encoding, hence code states with the same boundary data have identical predictions. -/
def boundaryIsSufficient (D : DephysHolographySufficientStatisticData) : Prop :=
  (∀ O : D.Obs, ∃ g : D.Boundary → D.Value,
    ∀ c : D.Code, D.codePrediction O c = g (D.boundaryEncode c)) ∧
    ∀ O : D.Obs, ∀ c c' : D.Code,
      D.boundaryEncode c = D.boundaryEncode c' →
        D.codePrediction O c = D.codePrediction O c'

end DephysHolographySufficientStatisticData

open DephysHolographySufficientStatisticData

/-- Paper label: `thm:dephys-holography-sufficient-statistic`. If every external observable on the
code subspace is reconstructed from boundary data, then all external predictions factor through the
boundary encoding, so the boundary is a sufficient statistic for code-space prediction. -/
theorem paper_dephys_holography_sufficient_statistic
    (D : DephysHolographySufficientStatisticData) : D.boundaryIsSufficient := by
  refine ⟨?_, ?_⟩
  · intro O
    refine ⟨D.boundaryPrediction O, ?_⟩
    intro c
    exact D.paper_label_dephys_holography_sufficient_statistic_reconstruction O c
  · intro O c c' hboundary
    calc
      D.codePrediction O c = D.boundaryPrediction O (D.boundaryEncode c) := by
        exact D.paper_label_dephys_holography_sufficient_statistic_reconstruction O c
      _ = D.boundaryPrediction O (D.boundaryEncode c') := by simp [hboundary]
      _ = D.codePrediction O c' := by
        exact (D.paper_label_dephys_holography_sufficient_statistic_reconstruction O c').symm

end Omega.Zeta
