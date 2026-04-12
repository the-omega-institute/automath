import Mathlib.Tactic

/-!
# Local alphabet budget and Smith prefix nonexchangeability seed values

Power-of-two vs power-of-ten comparisons and gap identities.
-/

namespace Omega.Conclusion

/-- Local alphabet Smith prefix nonexchangeability seeds.
    thm:conclusion-local-alphabet-budget-smith-prefix-budget-nonexchangeability -/
theorem paper_conclusion_local_alphabet_smith_prefix_nonexchangeability_seeds :
    (2 < 10) ∧
    (2 ^ 3 = 8 ∧ 10 ^ 3 = 1000) ∧
    (8 < 1000) ∧
    (2 ^ 9 = 512 ∧ 512 < 1000 ∧ 1000 < 1024 ∧ 2 ^ 10 = 1024) ∧
    (1024 - 1000 = 24) := by
  refine ⟨by omega, ⟨by norm_num, by norm_num⟩, by omega,
         ⟨by norm_num, by omega, by omega, by norm_num⟩, by omega⟩

/-- Minimal prime-infrastructure Smith atomic recovery seeds.
    This packages a finite counting seed together with a discrete Hessian-style
    arithmetic seed for the Smith-prefix budget discussion.
    prop:conclusion-minimal-prime-infrastructure-smith-atomic-recovery-seeds -/
theorem paper_conclusion_minimal_prime_infrastructure_smith_atomic_recovery_seeds :
    Nat.card (Fin 4) = 4 ∧
    (1 - 2 * 2 + 3 = (0 : ℤ)) ∧
    (4 - 2 * 9 + 16 = (2 : ℤ)) := by
  refine ⟨by simp, by norm_num, by norm_num⟩

end Omega.Conclusion
