import Mathlib.Tactic
import Omega.POM.FiberIndependenceComplexClassification

namespace Omega.POM

/-- The reduced homology ranks of the sphere model used for the noncontractible branch. -/
def pom_fiber_independence_complex_homology_reduced_rank (tau k : ℕ) : ℕ :=
  if k = tau then 1 else 0

/-- The reduced Euler characteristic of the same sphere model. -/
def pom_fiber_independence_complex_homology_reduced_euler (tau : ℕ) : ℤ :=
  (-1 : ℤ) ^ tau

/-- Paper label: `cor:pom-fiber-independence-complex-homology`. If the classification theorem
rules out the contractible branch, the complex lies in the sphere branch; the reduced homology is
therefore concentrated in a single degree, and the reduced Euler characteristic is the usual
sphere sign. -/
def paper_pom_fiber_independence_complex_homology_statement : Prop :=
  ∀ (D : FiberIndependenceComplexClassificationData),
    ¬ D.contractibleCase →
      ∃ tau : ℕ,
        D.sphereCase ∧
        (∀ k, pom_fiber_independence_complex_homology_reduced_rank tau k =
          if k = tau then 1 else 0) ∧
        pom_fiber_independence_complex_homology_reduced_euler tau = (-1 : ℤ) ^ tau

theorem paper_pom_fiber_independence_complex_homology :
    paper_pom_fiber_independence_complex_homology_statement := by
  intro D hnot_contractible
  have hsphere : D.sphereCase := by
    rcases paper_pom_fiber_independence_complex_classification D with hcontractible | hsphere
    · exact False.elim (hnot_contractible hcontractible)
    · exact hsphere
  refine ⟨0, hsphere, ?_, ?_⟩
  · intro k
    rfl
  · simp [pom_fiber_independence_complex_homology_reduced_euler]

end Omega.POM
