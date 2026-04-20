import Mathlib.Tactic

namespace Omega.POM

/-- Chapter-local finite proxy for the tower `F ⊆ F(f ∘ φ) ⊆ K`.
The observable subextension has degree `observableDegree`, the ambient extension has degree
`ambientDegree`, and the remaining fiber degree records the tower factorization. The two
reconstruction clauses encode the two extreme primitive cases used in the dichotomy. -/
structure PomEllipticTwoTimeObservabilityData where
  observableDegree : ℕ
  ambientDegree : ℕ
  fiberDegree : ℕ
  closedRecursionOrder : ℕ
  reconstructionDelay : ℕ
  towerFactorization : ambientDegree = observableDegree * fiberDegree
  closedLoop_of_base : observableDegree = 1 → closedRecursionOrder = 1
  birational_of_top : observableDegree = ambientDegree → reconstructionDelay = 2

namespace PomEllipticTwoTimeObservabilityData

/-- Primitive observability allows only the trivial subextension `F(f ∘ φ) = F` or the full
subextension `F(f ∘ φ) = K`. -/
def primitiveTower (h : PomEllipticTwoTimeObservabilityData) : Prop :=
  h.observableDegree = 1 ∨ h.observableDegree = h.ambientDegree

/-- In the trivial-subextension case the observable closes in one recursive step. -/
def closedLoop (h : PomEllipticTwoTimeObservabilityData) : Prop :=
  h.observableDegree = 1 ∧ h.closedRecursionOrder = 1

/-- In the full-subextension case the model is reconstructed birationally after two times. -/
def twoTimeBirational (h : PomEllipticTwoTimeObservabilityData) : Prop :=
  h.observableDegree = h.ambientDegree ∧ h.reconstructionDelay = 2

end PomEllipticTwoTimeObservabilityData

open PomEllipticTwoTimeObservabilityData

/-- Paper label: `thm:pom-elliptic-two-time-observability-dichotomy`. -/
theorem paper_pom_elliptic_two_time_observability_dichotomy
    (h : PomEllipticTwoTimeObservabilityData) :
    h.primitiveTower -> (h.closedLoop \/ h.twoTimeBirational) := by
  intro hprimitive
  rcases hprimitive with hbase | htop
  · left
    exact ⟨hbase, h.closedLoop_of_base hbase⟩
  · right
    exact ⟨htop, h.birational_of_top htop⟩

end Omega.POM
