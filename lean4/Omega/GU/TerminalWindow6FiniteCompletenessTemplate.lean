import Mathlib.Tactic
import Omega.GU.TerminalGamma6MultiplicityRigidity
import Omega.GU.TerminalGamma6Rigidity

namespace Omega.GU

/-- A finite audit of the window-6 terminal picture only needs three tagged witnesses. -/
abbrev TerminalWindow6AuditTriple (X : Type) :=
  Fin 3 → X

/-- Any multiplicity-preserving symmetry of the audited window-6 data that also fixes the chosen
labels pointwise must be trivial. -/
def terminalWindow6UniqueLabeling {X : Type} (Adj : X → X → Prop) (A : X → X → Nat)
    (label : X → Fin 6) : Prop :=
  ∀ σ : Equiv.Perm X,
    (∀ u v, A (σ u) (σ v) = A u v) →
    (∀ u v, 0 < A u v ↔ Adj u v) →
    (∀ x, label (σ x) = label x) →
    σ = Equiv.refl X

/-- On a finite audit triple, isomorphism reduces to an equality check. -/
def terminalWindow6FiniteIsomorphismDecidable {X : Type} [DecidableEq X]
    (audit₀ audit₁ : TerminalWindow6AuditTriple X) : Prop :=
  Nonempty (Decidable (audit₀ = audit₁))

/-- Finite window-6 completeness template: the Gamma6 rigidity and multiplicity-rigidity wrappers
force unique labeling, and finite audit triples admit a direct equality decision procedure.
    cor:terminal-window6-finite-completeness-template -/
theorem paper_terminal_window6_finite_completeness_template {X : Type} [Fintype X]
    [DecidableEq X] (Adj : X → X → Prop) (A : X → X → Nat) (label : X → Fin 6)
    (audit₀ audit₁ : TerminalWindow6AuditTriple X) (R : TerminalGamma6RigidityData)
    (hRigid : ∀ τ : Equiv.Perm X,
      (∀ a b, Adj a b ↔ Adj (τ a) (τ b)) → τ = Equiv.refl X) :
    terminalWindow6UniqueLabeling Adj A label ∧
      terminalWindow6FiniteIsomorphismDecidable audit₀ audit₁ := by
  have _ := paper_terminal_gamma6_rigidity R
  refine ⟨?_, ?_⟩
  · intro σ hPres hSupport _hLabel
    exact paper_terminal_gamma6_multiplicity_rigidity Adj A σ hRigid hSupport hPres
  · classical
    exact ⟨inferInstance⟩

end Omega.GU
