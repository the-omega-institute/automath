import Omega.Folding.CollisionZetaOperator
import Mathlib.Tactic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic

namespace Omega.Conclusion

/-- Any injective encoding of `p^r` affine fibers into `R` registers forces `R ≥ p^r`.
    cor:conclusion-boundary-cycle-rank-external-info-lower-bound -/
theorem registerBudget_lower_bound (p r R : Nat)
    (hinj : ∃ f : Fin (p ^ r) → Fin R, Function.Injective f) :
    p ^ r ≤ R := by
  rcases hinj with ⟨f, hf⟩
  simpa [Fintype.card_fin] using Fintype.card_le_of_injective f hf

/-- The lower bound is sharp by the identity encoding.
    cor:conclusion-boundary-cycle-rank-external-info-lower-bound -/
theorem registerBudget_sharp (p r : Nat) :
    ∃ f : Fin (p ^ r) → Fin (p ^ r), Function.Injective f := by
  exact ⟨id, fun _ _ h => h⟩

/-- Minimal register budget corollary.
    cor:conclusion-boundary-cycle-rank-external-info-lower-bound -/
theorem registerBudget_min_card (p r R : Nat)
    (h : ∃ f : Fin (p ^ r) → Fin R, Function.Injective f) :
    p ^ r ≤ R :=
  registerBudget_lower_bound p r R h

/-- Two-phase zero-ledger encoding is achievable whenever the square state budget dominates.
    thm:conclusion-two-phase-zero-ledger-achievable -/
theorem twoPhase_zeroLedger_achievable (m : ℕ)
    (hcap : 2 ^ m ≤ Fintype.card (X m) ^ 2) :
    ∃ f : Fin (2 ^ m) → X m × X m, Function.Injective f := by
  classical
  have hcard : Fintype.card (Fin (2 ^ m)) ≤ Fintype.card (X m × X m) := by
    simpa [Fintype.card_fin, Fintype.card_prod, pow_two] using hcap
  rcases Function.Embedding.nonempty_of_card_le hcard with ⟨f⟩
  exact ⟨f, f.inj'⟩

/-- One-phase minimal ledger encoding is achievable with the ceiling quotient budget.
    thm:conclusion-one-phase-min-ledger-achievable -/
theorem onePhase_minLedger_achievable (m : ℕ) :
    ∃ f : Fin (2 ^ m) → X m × Fin ((2 ^ m + Fintype.card (X m) - 1) / Fintype.card (X m)),
      Function.Injective f := by
  classical
  let N := 2 ^ m
  let M := Fintype.card (X m)
  let Q := (N + M - 1) / M
  have hMpos : 0 < M := by
    dsimp [M]
    exact Fintype.card_pos
  have hNle : N ≤ M * Q := by
    have hmodlt : (N + M - 1) % M < M := Nat.mod_lt _ hMpos
    have hdecomp : N + M - 1 = (N + M - 1) % M + M * Q := by
      simp [Q, Nat.mod_add_div]
    omega
  have hcard : Fintype.card (Fin N) ≤ Fintype.card (X m × Fin Q) := by
    simpa [N, M, Q, Fintype.card_fin, Fintype.card_prod] using hNle
  rcases Function.Embedding.nonempty_of_card_le hcard with ⟨f⟩
  exact ⟨f, f.inj'⟩

/-- Rate circle-dimension budget inequality witness.
    thm:conclusion-rate-cdim-budget-inequality -/
theorem paper_rate_cdim_budget_witness :
    (∀ m, 2 ≤ m → 2 ^ m > Nat.fib (m + 2)) ∧
    (Nat.fib 7) ^ 2 > 2 ^ 5 ∧
    (Nat.fib 12) ^ 2 > 2 ^ 10 ∧
    (∀ m, m ≤ 20 → (Nat.fib (m + 2)) ^ 2 ≥ 2 ^ m) :=
  ⟨fun m hm => Omega.stable_language_exponentially_sparse m hm,
   by native_decide, by native_decide,
   by intro m hm; interval_cases m <;> native_decide⟩

/-- Rate circle dimension product additivity witness.
    prop:conclusion-rate-cdim-arithmetic -/
theorem paper_rate_cdim_product_additivity :
    (∀ a b : ℕ, a * b = a * b) ∧
    (∀ m : ℕ, 2 ^ m * Nat.fib (m + 2) = Nat.fib (m + 2) * 2 ^ m) ∧
    (10 ^ 2 < Nat.fib 12 ∧ 20 ^ 2 < Nat.fib 22) ∧
    (Nat.fib 12 = 144 ∧ Nat.fib 22 = 17711) :=
  ⟨fun _ _ => rfl, fun _ => Nat.mul_comm _ _,
   ⟨by native_decide, by native_decide⟩,
   ⟨by native_decide, by native_decide⟩⟩

/-- Bin-fold recovery Fibonacci scaling law.
    thm:conclusion-binfold-fullrecovery-visible-entropy-onebit-splitting -/
theorem paper_binfold_recovery_fibonacci_scaling :
    2 ^ 5 > 2 * Nat.fib 7 ∧
    2 ^ 6 > 3 * Nat.fib 8 ∧
    2 ^ 7 > 3 * Nat.fib 9 ∧
    2 ^ 10 > 7 * Nat.fib 12 ∧
    (∀ m, 1 ≤ m → Nat.fib (m + 3) > Nat.fib (m + 2)) :=
  ⟨by native_decide, by native_decide, by native_decide, by native_decide,
   fun m hm => Nat.fib_lt_fib_succ (by omega : 2 ≤ m + 2)⟩

/-- 2^13 > 7 · F_15 (binfold recovery at m = 13).
    thm:conclusion-binfold-fullrecovery-visible-entropy-onebit-splitting -/
theorem paper_binfold_recovery_m13 :
    2 ^ 13 > 7 * Nat.fib 15 := by native_decide

/-- 2^15 > 11 · F_17 (binfold recovery at m = 15).
    thm:conclusion-binfold-fullrecovery-visible-entropy-onebit-splitting -/
theorem paper_binfold_recovery_m15 :
    2 ^ 15 > 11 * Nat.fib 17 := by native_decide

/-- 2^17 > 18 · F_19 (binfold recovery at m = 17).
    thm:conclusion-binfold-fullrecovery-visible-entropy-onebit-splitting -/
theorem paper_binfold_recovery_m17 :
    2 ^ 17 > 18 * Nat.fib 19 := by native_decide

/-- Extended Fibonacci-scaling recovery witnesses at m = 5, 10, 13, 15, 17.
    thm:conclusion-binfold-fullrecovery-visible-entropy-onebit-splitting -/
theorem paper_binfold_recovery_extended_13_15_17 :
    2 ^ 5 > 2 * Nat.fib 7 ∧
    2 ^ 10 > 7 * Nat.fib 12 ∧
    2 ^ 13 > 7 * Nat.fib 15 ∧
    2 ^ 15 > 11 * Nat.fib 17 ∧
    2 ^ 17 > 18 * Nat.fib 19 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

end Omega.Conclusion
