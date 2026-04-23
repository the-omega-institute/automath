import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Omega.POM.DerivedAuditedEvenMinsectorTopologicalPhase
import Omega.Zeta.AuditedEvenFirstCapacityKinkFibonacciJump

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-audited-even-firstkink-homotopy-purification`. -/
theorem paper_conclusion_audited_even_firstkink_homotopy_purification (m : Nat)
    (hm : m ∈ ({6, 8, 10, 12} : Finset Nat)) :
    (∀ {t : Real},
        0 <= t -> t <= (Omega.Zeta.auditedEvenFirstKink m : Real) ->
          Omega.Zeta.auditedEvenContinuousCapacity m t = ((Nat.fib (m + 2) : Nat) : Real) * t) ∧
      (m % 6 = 0 ->
        Omega.POM.auditedEvenMinsectorPhase m = Omega.POM.AuditedEvenMinsectorPhase.contractible) ∧
      ((m % 6 = 2 ∨ m % 6 = 4) ->
        Omega.POM.auditedEvenMinsectorPhase m = Omega.POM.AuditedEvenMinsectorPhase.sphereZero) := by
  rcases (by simpa using hm : m = 6 ∨ m = 8 ∨ m = 10 ∨ m = 12) with
    rfl | rfl | rfl | rfl
  · refine ⟨by
        intro t ht0 htk
        exact (Omega.Zeta.paper_xi_audited_even_first_capacity_kink_fibonacci_jump 6).1 ht0 htk,
      ?_, ?_⟩
    · intro _
      simpa using Omega.POM.paper_derived_audited_even_minsector_topological_phase.2.2.2.2.1
    · intro hmod
      exfalso
      omega
  · refine ⟨by
        intro t ht0 htk
        exact (Omega.Zeta.paper_xi_audited_even_first_capacity_kink_fibonacci_jump 8).1 ht0 htk,
      ?_, ?_⟩
    · intro hmod
      exfalso
      omega
    · intro _
      simpa using Omega.POM.paper_derived_audited_even_minsector_topological_phase.2.2.2.2.2.1
  · refine ⟨by
        intro t ht0 htk
        exact (Omega.Zeta.paper_xi_audited_even_first_capacity_kink_fibonacci_jump 10).1 ht0 htk,
      ?_, ?_⟩
    · intro hmod
      exfalso
      omega
    · intro _
      simpa using Omega.POM.paper_derived_audited_even_minsector_topological_phase.2.2.2.2.2.2.1
  · refine ⟨by
        intro t ht0 htk
        exact (Omega.Zeta.paper_xi_audited_even_first_capacity_kink_fibonacci_jump 12).1 ht0 htk,
      ?_, ?_⟩
    · intro _
      simpa using Omega.POM.paper_derived_audited_even_minsector_topological_phase.2.2.2.2.2.2.2
    · intro hmod
      exfalso
      omega

end Omega.Conclusion
