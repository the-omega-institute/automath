import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.GroupUnification

/-- A single audit witness packages the three finite coordinates from the paper: a Sturm-bounded
Fourier/Hecke index, a finite Dirichlet layer, and a bounded counterterm budget slot.
    thm:audit-finite-decidability-sturm-finite-layer -/
abbrev AuditWitness (sturmBound dirichletLayers countertermBudget : ℕ) :=
  Fin (sturmBound + 1) × Fin (dirichletLayers + 1) × Fin (countertermBudget + 1)

/-- The global matching problem asks whether the candidate and target audit readouts agree on every
finite witness in the packaged audit space. -/
def GlobalAuditMatch
    {sturmBound dirichletLayers countertermBudget : ℕ}
    (candidate target : AuditWitness sturmBound dirichletLayers countertermBudget → ℤ) : Prop :=
  ∀ w, candidate w = target w

/-- Deterministic finite audit search for the global matching problem. -/
noncomputable def finiteAuditSearch
    {sturmBound dirichletLayers countertermBudget : ℕ}
    (candidate target : AuditWitness sturmBound dirichletLayers countertermBudget → ℤ) : Bool :=
  by
    classical
    exact decide (GlobalAuditMatch candidate target)

/-- Packaging the Sturm bound, the finite Dirichlet layer closure, and the counterterm
strictification budget into one finite witness type turns the global matching problem into a
decidable finite search over that witness space.
    thm:audit-finite-decidability-sturm-finite-layer -/
theorem paper_audit_finite_decidability_sturm_finite_layer
    (sturmBound dirichletLayers countertermBudget : ℕ)
    (candidate target :
      AuditWitness sturmBound dirichletLayers countertermBudget → ℤ) :
    (Finset.univ :
      Finset (AuditWitness sturmBound dirichletLayers countertermBudget)).card =
        Fintype.card (AuditWitness sturmBound dirichletLayers countertermBudget) ∧
      (∀ w : AuditWitness sturmBound dirichletLayers countertermBudget,
        w ∈ (Finset.univ :
          Finset (AuditWitness sturmBound dirichletLayers countertermBudget))) ∧
      (finiteAuditSearch candidate target = true ↔ GlobalAuditMatch candidate target) := by
  classical
  refine ⟨by simp, ?_, ?_⟩
  · intro w
    simp
  · simp [finiteAuditSearch, GlobalAuditMatch]

end Omega.GroupUnification
