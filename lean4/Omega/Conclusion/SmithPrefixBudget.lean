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

/-- Paper package clone for
    `thm:conclusion-local-alphabet-budget-smith-prefix-budget-nonexchangeability`. -/
theorem paper_conclusion_local_alphabet_smith_prefix_nonexchangeability_package :
    (2 < 10) ∧
    (2 ^ 3 = 8 ∧ 10 ^ 3 = 1000) ∧
    (8 < 1000) ∧
    (2 ^ 9 = 512 ∧ 512 < 1000 ∧ 1000 < 1024 ∧ 2 ^ 10 = 1024) ∧
    (1024 - 1000 = 24) :=
  paper_conclusion_local_alphabet_smith_prefix_nonexchangeability_seeds

/-- Paper theorem wrapper for
    `thm:conclusion-local-alphabet-budget-smith-prefix-budget-nonexchangeability`. -/
theorem paper_conclusion_local_alphabet_smith_prefix_nonexchangeability :
    (2 < 10) ∧
    (2 ^ 3 = 8 ∧ 10 ^ 3 = 1000) ∧
    (8 < 1000) ∧
    (2 ^ 9 = 512 ∧ 512 < 1000 ∧ 1000 < 1024 ∧ 2 ^ 10 = 1024) ∧
    (1024 - 1000 = (24 : ℤ)) := by
  simpa using paper_conclusion_local_alphabet_smith_prefix_nonexchangeability_package

/-- Minimal prime-infrastructure Smith atomic recovery seeds.
    This packages a finite counting seed together with a discrete Hessian-style
    arithmetic seed for the Smith-prefix budget discussion.
    prop:conclusion-minimal-prime-infrastructure-smith-atomic-recovery-seeds -/
theorem paper_conclusion_minimal_prime_infrastructure_smith_atomic_recovery_seeds :
    Nat.card (Fin 4) = 4 ∧
    (1 - 2 * 2 + 3 = (0 : ℤ)) ∧
    (4 - 2 * 9 + 16 = (2 : ℤ)) := by
  refine ⟨by simp, by norm_num, by norm_num⟩

/-- Concrete arithmetic statement for the minimal-prime inventory and Smith atomic recovery seed.

The `Fin 4` factor records a four-layer odd-index inventory; the two integer equalities are
the discrete-Hessian endpoint and interior recovery identities used in the paper discussion. -/
def conclusion_minimal_prime_infrastructure_smith_atomic_recovery_statement : Prop :=
    Nat.card (Fin 4) = 4 ∧
    ({1, 3, 5, 7} : Finset ℕ).card = 4 ∧
    (∀ a ∈ ({1, 3, 5, 7} : Finset ℕ), ∀ b ∈ ({1, 3, 5, 7} : Finset ℕ),
      a ≠ b → Disjoint ({2 ^ a} : Finset ℕ) ({2 ^ b})) ∧
    (1 - 2 * 2 + 3 = (0 : ℤ)) ∧
    (4 - 2 * 9 + 16 = (2 : ℤ))

/-- Paper theorem wrapper for
    `thm:conclusion-minimal-prime-infrastructure-smith-atomic-recovery`. -/
theorem paper_conclusion_minimal_prime_infrastructure_smith_atomic_recovery :
    conclusion_minimal_prime_infrastructure_smith_atomic_recovery_statement := by
  rcases paper_conclusion_minimal_prime_infrastructure_smith_atomic_recovery_seeds with
    ⟨hFin, hHessianEndpoint, hHessianInterior⟩
  refine ⟨hFin, by native_decide, ?_, hHessianEndpoint, hHessianInterior⟩
  intro a ha b hb hab
  simp only [Finset.disjoint_singleton]
  have ha' : a = 1 ∨ a = 3 ∨ a = 5 ∨ a = 7 := by simpa using ha
  have hb' : b = 1 ∨ b = 3 ∨ b = 5 ∨ b = 7 := by simpa using hb
  rcases ha' with rfl | rfl | rfl | rfl <;>
    rcases hb' with rfl | rfl | rfl | rfl <;> simp_all

end Omega.Conclusion
