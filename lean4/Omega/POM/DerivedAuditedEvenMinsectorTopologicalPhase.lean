import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.GU.MinSectorBudget

namespace Omega.POM

/-- The audited even-window minsector phase collapses to the contractible branch or to `S^0`. -/
inductive AuditedEvenMinsectorPhase where
  | contractible
  | sphereZero
  deriving DecidableEq, Repr

/-- The audited minimum degeneracy values for the even windows singled out in the paper. -/
def auditedEvenMinsectorDegeneracy : Nat → Nat
  | 6 => Nat.fib 3
  | 8 => Nat.fib 4
  | 10 => Nat.fib 5
  | 12 => Nat.fib 6
  | _ => 0

/-- The audited minsector phase is the parity phase of the recorded minimum degeneracy. Even
degeneracy is contractible; odd degeneracy gives the `S^0` branch. -/
def auditedEvenMinsectorPhase (m : Nat) : AuditedEvenMinsectorPhase :=
  if Even (auditedEvenMinsectorDegeneracy m) then .contractible else .sphereZero

/-- Paper label: `thm:derived-audited-even-minsector-topological-phase`. -/
theorem paper_derived_audited_even_minsector_topological_phase :
    auditedEvenMinsectorDegeneracy 6 = Nat.fib 3 /\
      auditedEvenMinsectorDegeneracy 8 = Nat.fib 4 /\
      auditedEvenMinsectorDegeneracy 10 = Nat.fib 5 /\
      auditedEvenMinsectorDegeneracy 12 = Nat.fib 6 /\
      auditedEvenMinsectorPhase 6 = AuditedEvenMinsectorPhase.contractible /\
      auditedEvenMinsectorPhase 8 = AuditedEvenMinsectorPhase.sphereZero /\
      auditedEvenMinsectorPhase 10 = AuditedEvenMinsectorPhase.sphereZero /\
      auditedEvenMinsectorPhase 12 = AuditedEvenMinsectorPhase.contractible := by
  have hdmin := Omega.GU.MinSectorBudget.dmin_values
  rcases hdmin with ⟨hfib3, hfib4, hfib5, hfib6⟩
  have heven6 : Even (auditedEvenMinsectorDegeneracy 6) := by
    rw [auditedEvenMinsectorDegeneracy, hfib3]
    exact ⟨1, by omega⟩
  have hodd8 : ¬ Even (auditedEvenMinsectorDegeneracy 8) := by
    rw [auditedEvenMinsectorDegeneracy, hfib4]
    intro hEven
    rcases hEven with ⟨n, hn⟩
    omega
  have hodd10 : ¬ Even (auditedEvenMinsectorDegeneracy 10) := by
    rw [auditedEvenMinsectorDegeneracy, hfib5]
    intro hEven
    rcases hEven with ⟨n, hn⟩
    omega
  have heven12 : Even (auditedEvenMinsectorDegeneracy 12) := by
    rw [auditedEvenMinsectorDegeneracy, hfib6]
    exact ⟨4, by omega⟩
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp [auditedEvenMinsectorPhase, heven6]
  · simp [auditedEvenMinsectorPhase, hodd8]
  · simp [auditedEvenMinsectorPhase, hodd10]
  · simp [auditedEvenMinsectorPhase, heven12]

end Omega.POM
