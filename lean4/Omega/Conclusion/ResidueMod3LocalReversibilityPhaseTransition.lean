import Mathlib.Tactic
import Omega.Core.Fib

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-residue-mod3-local-reversibility-phase-transition`. -/
theorem paper_conclusion_residue_mod3_local_reversibility_phase_transition (m : ℕ)
    (uniqueRecovery localDefect : Prop)
    (hUnique : ¬ (2 ∣ Nat.fib (m + 2)) → uniqueRecovery)
    (hDefect : m % 3 = 1 → localDefect) :
    ((¬ (2 ∣ Nat.fib (m + 2))) ↔ m % 3 ≠ 1) ∧
      (m % 3 ≠ 1 → uniqueRecovery) ∧
      (m % 3 = 1 → localDefect) := by
  have hshift : (3 ∣ m + 2) ↔ m % 3 = 1 := by
    constructor
    · intro h
      have hmod : (m + 2) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
      omega
    · intro hm
      exact Nat.dvd_of_mod_eq_zero (by omega)
  have hphase : (¬ (2 ∣ Nat.fib (m + 2))) ↔ m % 3 ≠ 1 :=
    (Omega.fib_odd_iff_not_three_dvd (m + 2)).trans (not_congr hshift)
  refine ⟨hphase, ?_, hDefect⟩
  intro hm
  exact hUnique (hphase.mpr hm)

end Omega.Conclusion
