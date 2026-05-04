import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-localized-solenoid-finitewindow-periodic-audit-blind-primes`. -/
theorem paper_conclusion_localized_solenoid_finitewindow_periodic_audit_blind_primes
    (Q : Finset (ℕ × ℕ)) :
    ∀ M, ∃ p, M ≤ p ∧ Nat.Prime p ∧
      p ∉ Q.biUnion (fun q => (q.1 ^ q.2 - 1).primeFactors) := by
  intro M
  let bad : Finset ℕ := Q.biUnion (fun q => (q.1 ^ q.2 - 1).primeFactors)
  obtain ⟨p, hpLarge, hpPrime⟩ := Nat.exists_infinite_primes (max M (bad.sup id + 1))
  have hM : M ≤ p := le_trans (le_max_left _ _) hpLarge
  have hpNotMem : p ∉ bad := by
    intro hpMem
    have hpLeSup : p ≤ bad.sup id := by
      simpa using (Finset.le_sup (f := id) hpMem)
    have hSupLt : bad.sup id < p := by
      exact Nat.lt_of_succ_le (le_trans (le_max_right _ _) hpLarge)
    omega
  exact ⟨p, hM, hpPrime, hpNotMem⟩

end Omega.Conclusion
