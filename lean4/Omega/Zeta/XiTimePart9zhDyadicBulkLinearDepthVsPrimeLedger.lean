import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.CoprimeLedgerPrimorialOptimality

namespace Omega.Zeta

/-- Dyadic bulk words of length `T`. -/
abbrev DyadicBulkWord (T : ℕ) := Fin T → Fin 2

/-- Prefix observed at depth `m`. -/
def dyadicBulkPrefix {T : ℕ} (m : ℕ) (w : DyadicBulkWord T) : Fin (min m T) → Fin 2 :=
  fun i => w ⟨i.1, lt_of_lt_of_le i.2 (Nat.min_le_right _ _)⟩

/-- Two words are separated at depth `m` when their length-`m` prefixes differ. -/
def dyadicBulkSeparatedAtDepth {T : ℕ} (m : ℕ) (x y : DyadicBulkWord T) : Prop :=
  dyadicBulkPrefix m x ≠ dyadicBulkPrefix m y

/-- The exact dyadic bulk depth is linear in the word length. -/
def dyadicBulkLinearDepth (T : ℕ) : ℕ := T

/-- The all-zero word. -/
def dyadicBulkZeroWord (T : ℕ) : DyadicBulkWord T := fun _ => 0

/-- Swap the last dyadic symbol from `0` to `1`. -/
def dyadicBulkLastSwapWord (T : ℕ) : DyadicBulkWord (T + 1) :=
  fun i => if h : i.1 = T then ⟨1, by decide⟩ else 0

private lemma dyadicBulkSeparated_full {T : ℕ} {x y : DyadicBulkWord T} (hxy : x ≠ y) :
    dyadicBulkSeparatedAtDepth T x y := by
  intro hprefix
  apply hxy
  funext i
  have hval := congrArg (fun f => f ⟨i.1, by simp [i.2]⟩) hprefix
  simpa [dyadicBulkPrefix] using hval

private lemma dyadicBulkPrefix_lastSwap_eq_zero (T : ℕ) :
    dyadicBulkPrefix T (dyadicBulkLastSwapWord T) =
      dyadicBulkPrefix T (dyadicBulkZeroWord (T + 1)) := by
  funext i
  have hi : i.1 < T := lt_of_lt_of_le i.2 (Nat.min_le_left _ _)
  have hne : i.1 ≠ T := ne_of_lt hi
  simp [dyadicBulkPrefix, dyadicBulkLastSwapWord, dyadicBulkZeroWord, hne]

private lemma dyadicBulkZero_ne_lastSwap (T : ℕ) :
    dyadicBulkZeroWord (T + 1) ≠ dyadicBulkLastSwapWord T := by
  intro hEq
  have hval := congrArg (fun f => f ⟨T, Nat.lt_succ_self T⟩) hEq
  simp [dyadicBulkZeroWord, dyadicBulkLastSwapWord] at hval

private lemma dyadicBulkNotSeparated_pred (T : ℕ) :
    ¬ dyadicBulkSeparatedAtDepth T (dyadicBulkZeroWord (T + 1)) (dyadicBulkLastSwapWord T) := by
  intro hsep
  exact hsep (dyadicBulkPrefix_lastSwap_eq_zero T).symm

private theorem primeLedger_log_lower (T : ℕ) :
    ((T + 1 : ℝ) * Real.log (T + 1) - (T + 1) +
        Real.log (T + 1) / 2 + Real.log (2 * Real.pi) / 2) ≤
      Real.log (Omega.POM.firstPrimeProduct T) := by
  have hq : ∀ i : Fin T, 2 ≤ Omega.POM.nthPrime i := by
    intro i
    exact (Omega.POM.nthPrime_prime i).two_le
  have hpair : Pairwise fun i j : Fin T => Nat.Coprime (Omega.POM.nthPrime i) (Omega.POM.nthPrime j) := by
    intro i j hij
    refine (Nat.coprime_primes (Omega.POM.nthPrime_prime i) (Omega.POM.nthPrime_prime j)).2 ?_
    intro hEq
    apply hij
    ext
    exact (Nat.nth_strictMono Nat.infinite_setOf_prime).injective hEq
  exact (Omega.POM.paper_pom_coprime_ledger_primorial_optimality
    T 0 (fun i : Fin T => Omega.POM.nthPrime i) hq hpair).2.2

private theorem primeLedger_ratio_lower (T : ℕ) :
    (((T + 1 : ℝ) * Real.log (T + 1) - (T + 1) +
          Real.log (T + 1) / 2 + Real.log (2 * Real.pi) / 2) / (T + 1 : ℝ)) ≤
      Real.log (Omega.POM.firstPrimeProduct T) / (dyadicBulkLinearDepth (T + 1) : ℝ) := by
  have hmain := primeLedger_log_lower T
  have hdiv :
      (((T + 1 : ℝ) * Real.log (T + 1) - (T + 1) +
            Real.log (T + 1) / 2 + Real.log (2 * Real.pi) / 2) / (T + 1 : ℝ)) ≤
        Real.log (Omega.POM.firstPrimeProduct T) / (T + 1 : ℝ) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hmain (by positivity)
  simpa [dyadicBulkLinearDepth] using hdiv

/-- At full depth every dyadic bulk word of length `T + 1` is separated by its prefix, while depth
`T` cannot distinguish a last-symbol swap. Therefore the exact bulk depth is linear, whereas the
prime-ledger log cost is bounded below by the primorial `T log T` estimate, giving the advertised
per-depth ratio lower bound.
    thm:xi-time-part9zh-dyadic-bulk-linear-depth-vs-prime-ledger -/
theorem paper_xi_time_part9zh_dyadic_bulk_linear_depth_vs_prime_ledger (T : ℕ) :
    (∀ x y : DyadicBulkWord (T + 1), x ≠ y → dyadicBulkSeparatedAtDepth (T + 1) x y) ∧
      (∃ x y : DyadicBulkWord (T + 1), x ≠ y ∧ ¬ dyadicBulkSeparatedAtDepth T x y) ∧
      dyadicBulkLinearDepth (T + 1) = T + 1 ∧
      (((T + 1 : ℝ) * Real.log (T + 1) - (T + 1) +
          Real.log (T + 1) / 2 + Real.log (2 * Real.pi) / 2) ≤
        Real.log (Omega.POM.firstPrimeProduct T)) ∧
      ((((T + 1 : ℝ) * Real.log (T + 1) - (T + 1) +
            Real.log (T + 1) / 2 + Real.log (2 * Real.pi) / 2) / (T + 1 : ℝ)) ≤
        Real.log (Omega.POM.firstPrimeProduct T) / (dyadicBulkLinearDepth (T + 1) : ℝ)) := by
  refine ⟨?_, ?_, rfl, primeLedger_log_lower T, primeLedger_ratio_lower T⟩
  · intro x y hxy
    exact dyadicBulkSeparated_full hxy
  · refine ⟨dyadicBulkZeroWord (T + 1), dyadicBulkLastSwapWord T, dyadicBulkZero_ne_lastSwap T, ?_⟩
    exact dyadicBulkNotSeparated_pred T

end Omega.Zeta
