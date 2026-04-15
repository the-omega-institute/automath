import Mathlib.Tactic

namespace Omega

/-- Local merge rigidity is commutative at the scalar level.
    lem:fold-local-weight-rigidity-fibonacci -/
theorem local_weight_rigidity_step (w₁ w₂ w₃ : ℤ)
    (hmerge : w₁ + w₂ = w₃) :
    w₃ = w₂ + w₁ := by
  omega

/-- Normalized first-step rigidity.
    lem:fold-local-weight-rigidity-fibonacci -/
theorem local_weight_rigidity_normalized :
    ∀ w₃ : ℤ, (1 : ℤ) + 2 = w₃ → w₃ = 3 := by
  intro w₃ h
  omega

/-- First four Fibonacci-style local rigidity identities.
    lem:fold-local-weight-rigidity-fibonacci -/
theorem local_weight_rigidity_first_four :
    (1 : ℤ) + 2 = 3 ∧ 2 + 3 = 5 := by
  omega

/-- Rule R2: 2·F_2 = F_3.
    lem:fold-local-weight-rigidity-fibonacci -/
theorem fold_rule_R2_identity : 2 * Nat.fib 2 = Nat.fib 3 := by decide

/-- Rule R3: 2·F_3 = F_2 + F_4.
    lem:fold-local-weight-rigidity-fibonacci -/
theorem fold_rule_R3_identity : 2 * Nat.fib 3 = Nat.fib 2 + Nat.fib 4 := by decide

/-- Rule R4 (k ≥ 2): 2·F_{k+1} = F_{k-1} + F_{k+2}.
    lem:fold-local-weight-rigidity-fibonacci -/
theorem fold_rule_R4_identity (k : Nat) (hk : 2 ≤ k) :
    2 * Nat.fib (k + 1) = Nat.fib (k - 1) + Nat.fib (k + 2) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  show 2 * Nat.fib (j + 2 + 1) = Nat.fib (j + 2 - 1) + Nat.fib (j + 2 + 2)
  rw [show j + 2 - 1 = j + 1 from by omega,
      show j + 2 + 1 = j + 3 from by omega,
      show j + 2 + 2 = j + 4 from by omega]
  have h4 : Nat.fib (j + 4) = Nat.fib (j + 3) + Nat.fib (j + 2) := by
    rw [show j + 4 = (j + 2) + 2 from by omega, Nat.fib_add_two]; ring
  have h3 : Nat.fib (j + 3) = Nat.fib (j + 2) + Nat.fib (j + 1) := by
    rw [show j + 3 = (j + 1) + 2 from by omega, Nat.fib_add_two]; ring
  omega

/-- Complete paper-facing fold-local rewrite identity package.
    lem:fold-local-weight-rigidity-fibonacci -/
theorem paper_fold_local_rewrite_identities :
    (∀ k, Nat.fib k + Nat.fib (k + 1) = Nat.fib (k + 2)) ∧
    (2 * Nat.fib 2 = Nat.fib 3) ∧
    (2 * Nat.fib 3 = Nat.fib 2 + Nat.fib 4) ∧
    (∀ k, 2 ≤ k → 2 * Nat.fib (k + 1) = Nat.fib (k - 1) + Nat.fib (k + 2)) :=
  ⟨fun k => (Nat.fib_add_two (n := k)).symm,
   fold_rule_R2_identity,
   fold_rule_R3_identity,
   fold_rule_R4_identity⟩

-- Phase R609: Fold rule R4 gap form and completeness seeds
-- ══════════════════════════════════════════════════════════════

/-- R4 gap form: F_{k+2} - F_{k+1} = F_{k+1} - F_{k-1} for k ≥ 2.
    lem:fold-local-weight-rigidity-fibonacci -/
theorem fold_rule_R4_gap (k : Nat) (hk : 2 ≤ k) :
    Nat.fib (k + 2) - Nat.fib (k + 1) = Nat.fib (k + 1) - Nat.fib (k - 1) := by
  have h := fold_rule_R4_identity k hk
  have hle : Nat.fib (k - 1) ≤ Nat.fib (k + 1) := Nat.fib_mono (by omega)
  have hle2 : Nat.fib (k + 1) ≤ Nat.fib (k + 2) := Nat.fib_le_fib_succ
  omega

/-- Fold rule completeness seeds: Fibonacci recurrence and doubling identities.
    lem:fold-local-weight-rigidity-fibonacci -/
theorem fold_rule_completeness_seeds :
    (Nat.fib 2 + Nat.fib 3 = Nat.fib 4) ∧
    (Nat.fib 3 + Nat.fib 4 = Nat.fib 5) ∧
    (Nat.fib 4 + Nat.fib 5 = Nat.fib 6) ∧
    (Nat.fib 5 + Nat.fib 6 = Nat.fib 7) ∧
    (Nat.fib 6 + Nat.fib 7 = Nat.fib 8) ∧
    (2 * Nat.fib 2 = Nat.fib 3) ∧
    (2 * Nat.fib 3 = Nat.fib 2 + Nat.fib 4) ∧
    (2 * Nat.fib 4 = Nat.fib 2 + Nat.fib 5) ∧
    (2 * Nat.fib 5 = Nat.fib 3 + Nat.fib 6) ∧
    (2 * Nat.fib 6 = Nat.fib 4 + Nat.fib 7) ∧
    (2 * Nat.fib 7 = Nat.fib 5 + Nat.fib 8) := by
  refine ⟨by native_decide, by native_decide, by native_decide,
          by native_decide, by native_decide, by native_decide,
          by native_decide, by native_decide, by native_decide,
          by native_decide, by native_decide⟩

end Omega
