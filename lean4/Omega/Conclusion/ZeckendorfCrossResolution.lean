import Omega.Folding.BoundaryLayer
import Omega.Folding.ZeckendorfSignature

open Omega X

namespace Omega.Conclusion

/-- The two index families in the closed `15F_n` and `16F_n` decompositions have pairwise
non-adjacent Fibonacci indices. Each conjunct records one lower-index-plus-two gap. -/
def conclusion_zeckendorf_15_16_closed_canonical_indices (n : Nat) : Prop :=
    (n + 2 + 2 ≤ n + 5) ∧ (n + 2 ≤ n + 5) ∧
    (n - 3 + 2 ≤ n + 5) ∧ (n - 6 + 2 ≤ n + 5) ∧
    (n + 2 ≤ n + 2) ∧ (n - 3 + 2 ≤ n + 2) ∧
    (n - 6 + 2 ≤ n + 2) ∧ (n - 3 + 2 ≤ n) ∧
    (n - 6 + 2 ≤ n) ∧ (n - 6 + 2 ≤ n - 3) ∧
    (n + 3 + 2 ≤ n + 5) ∧ (n - 1 + 2 ≤ n + 5) ∧
    (n - 6 + 2 ≤ n + 5) ∧ (n - 1 + 2 ≤ n + 3) ∧
    (n - 6 + 2 ≤ n + 3) ∧ (n - 6 + 2 ≤ n - 1)

/-- The offsets in the closed `15F_n` and `16F_n` decompositions are pairwise non-adjacent for
the stable range `n ≥ 8`. -/
lemma conclusion_zeckendorf_15_16_closed_canonical_indices_of_le
    (n : Nat) (hn : 8 ≤ n) :
    conclusion_zeckendorf_15_16_closed_canonical_indices n := by
  unfold conclusion_zeckendorf_15_16_closed_canonical_indices
  repeat constructor <;> omega

/-- Paper-facing closed Zeckendorf identities for `15F_n` and `16F_n`, together with the
canonical-index gap check.
    thm:conclusion-zeckendorf-15-16-closed -/
theorem paper_conclusion_zeckendorf_15_16_closed (n : Nat) (hn : 8 ≤ n) :
    15 * Nat.fib n = Nat.fib (n + 5) + Nat.fib (n + 2) + Nat.fib n +
      Nat.fib (n - 3) + Nat.fib (n - 6) ∧
    16 * Nat.fib n = Nat.fib (n + 5) + Nat.fib (n + 3) + Nat.fib (n - 1) +
      Nat.fib (n - 6) ∧
    conclusion_zeckendorf_15_16_closed_canonical_indices n := by
  exact ⟨Omega.ZeckSig.zeckendorf_15Fn_general n hn,
    Omega.ZeckSig.zeckendorf_16Fn_general n hn,
    conclusion_zeckendorf_15_16_closed_canonical_indices_of_le n hn⟩

/-- Paper-facing wrapper for the verified `15 → 16` Fibonacci carry identity.
    prop:conclusion-zeckendorf-15to16-carry -/
theorem paper_conclusion_zeckendorf_15to16_carry (n : Nat) (hn : 5 ≤ n) :
    Nat.fib (n + 2) + 2 * Nat.fib n + Nat.fib (n - 3) =
    Nat.fib (n + 3) + Nat.fib (n - 1) := by
  exact Omega.ZeckSig.fib_15to16_carry n hn

set_option maxHeartbeats 400000 in
/-- Paper-facing cross-resolution identities obtained by combining the verified `15F_n` / `16F_n`
Zeckendorf seeds with `|X_m| = F_{m+2}` and `|X_m^{bdry}| = F_{m-2}` in the audited range
`m = 10, 11, 12`.
    cor:conclusion-zeckendorf-15-16-cross-resolution -/
theorem paper_conclusion_zeckendorf_15_16_cross_resolution :
    (15 * cBoundaryCount 10 =
      Fintype.card (X 11) + Fintype.card (X 8) + Fintype.card (X 6) + Fintype.card (X 3) +
        Fintype.card (X 0)) ∧
    (16 * cBoundaryCount 10 =
      Fintype.card (X 11) + Fintype.card (X 9) + Fintype.card (X 5) + Fintype.card (X 0)) ∧
    (15 * cBoundaryCount 11 =
      Fintype.card (X 12) + Fintype.card (X 9) + Fintype.card (X 7) + Fintype.card (X 4) +
        Fintype.card (X 1)) ∧
    (16 * cBoundaryCount 11 =
      Fintype.card (X 12) + Fintype.card (X 10) + Fintype.card (X 6) + Fintype.card (X 1)) ∧
    (15 * cBoundaryCount 12 =
      Fintype.card (X 13) + Fintype.card (X 10) + Fintype.card (X 8) + Fintype.card (X 5) +
        Fintype.card (X 2)) ∧
    (16 * cBoundaryCount 12 =
      Fintype.card (X 13) + Fintype.card (X 11) + Fintype.card (X 7) + Fintype.card (X 2)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cBoundaryCount_eq_fib_general 10 (by omega), X.card_eq_fib 11, X.card_eq_fib 8,
      X.card_eq_fib 6, X.card_eq_fib 3, X.card_eq_fib 0]
    exact Omega.ZeckSig.zeckendorf_15Fn_instances.1
  · rw [cBoundaryCount_eq_fib_general 10 (by omega), X.card_eq_fib 11, X.card_eq_fib 9,
      X.card_eq_fib 5, X.card_eq_fib 0]
    exact Omega.ZeckSig.zeckendorf_16Fn_instances.1
  · rw [cBoundaryCount_eq_fib_general 11 (by omega), X.card_eq_fib 12, X.card_eq_fib 9,
      X.card_eq_fib 7, X.card_eq_fib 4, X.card_eq_fib 1]
    exact Omega.ZeckSig.zeckendorf_15Fn_instances.2.1
  · rw [cBoundaryCount_eq_fib_general 11 (by omega), X.card_eq_fib 12, X.card_eq_fib 10,
      X.card_eq_fib 6, X.card_eq_fib 1]
    exact Omega.ZeckSig.zeckendorf_16Fn_instances.2.1
  · rw [cBoundaryCount_eq_fib_general 12 (by omega), X.card_eq_fib 13, X.card_eq_fib 10,
      X.card_eq_fib 8, X.card_eq_fib 5, X.card_eq_fib 2]
    exact Omega.ZeckSig.zeckendorf_15Fn_instances.2.2
  · rw [cBoundaryCount_eq_fib_general 12 (by omega), X.card_eq_fib 13, X.card_eq_fib 11,
      X.card_eq_fib 7, X.card_eq_fib 2]
    exact Omega.ZeckSig.zeckendorf_16Fn_instances.2.2

/-- Stable-range index set in the closed Zeckendorf expansion of `15F_n`. -/
def conclusion_zeckendorf_resolution_lock_m6_stable_indices (n : Nat) : Finset Nat :=
  {n + 5, n + 2, n, n - 3, n - 6}

/-- Finite witnesses for the remaining audited cases `4 ≤ n ≤ 7`. -/
def conclusion_zeckendorf_resolution_lock_m6_finite_indices (n : Nat) : Finset Nat :=
  match n with
  | 4 => {9, 6, 4}
  | 5 => {10, 7, 5, 3}
  | 6 => {11, 8, 6, 3}
  | 7 => {12, 9, 7, 4, 2}
  | _ => ∅

/-- A pair of visible `F_4` and `F_6` terms is present in an index set. -/
def conclusion_zeckendorf_resolution_lock_m6_has_visible_pair (S : Finset Nat) : Prop :=
  4 ∈ S ∧ 6 ∈ S

/-- Concrete paper-facing statement for the `m = 6` Zeckendorf resolution lock. The variable
`n = m - 2` is used, so the locked case is `n = 4`. -/
def conclusion_zeckendorf_resolution_lock_m6_statement : Prop :=
  (15 * Nat.fib 4 =
      (conclusion_zeckendorf_resolution_lock_m6_finite_indices 4).sum Nat.fib ∧
    conclusion_zeckendorf_resolution_lock_m6_has_visible_pair
      (conclusion_zeckendorf_resolution_lock_m6_finite_indices 4)) ∧
  (∀ n : Nat, 4 ≤ n → n ≤ 7 → n ≠ 4 →
    15 * Nat.fib n =
        (conclusion_zeckendorf_resolution_lock_m6_finite_indices n).sum Nat.fib ∧
      ¬ conclusion_zeckendorf_resolution_lock_m6_has_visible_pair
        (conclusion_zeckendorf_resolution_lock_m6_finite_indices n)) ∧
  (∀ n : Nat, 8 ≤ n →
    15 * Nat.fib n = Nat.fib (n + 5) + Nat.fib (n + 2) + Nat.fib n +
        Nat.fib (n - 3) + Nat.fib (n - 6) ∧
      ¬ conclusion_zeckendorf_resolution_lock_m6_has_visible_pair
        (conclusion_zeckendorf_resolution_lock_m6_stable_indices n))

/-- Paper-facing wrapper for the `m = 6` Zeckendorf resolution lock.
    thm:conclusion-zeckendorf-resolution-lock-m6 -/
theorem paper_conclusion_zeckendorf_resolution_lock_m6 :
    conclusion_zeckendorf_resolution_lock_m6_statement := by
  unfold conclusion_zeckendorf_resolution_lock_m6_statement
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · simpa [conclusion_zeckendorf_resolution_lock_m6_finite_indices] using
        Omega.ZeckSig.zeckendorf_resolution_lock_m6
    · simp [conclusion_zeckendorf_resolution_lock_m6_has_visible_pair,
        conclusion_zeckendorf_resolution_lock_m6_finite_indices]
  · intro n hn4 hn7 hn_ne
    have hn_cases : n = 5 ∨ n = 6 ∨ n = 7 := by omega
    rcases hn_cases with rfl | rfl | rfl <;>
      simp [conclusion_zeckendorf_resolution_lock_m6_has_visible_pair,
        conclusion_zeckendorf_resolution_lock_m6_finite_indices] <;>
      norm_num [Nat.fib]
  · intro n hn
    constructor
    · exact Omega.ZeckSig.zeckendorf_15Fn_general n hn
    · intro hpair
      rcases hpair with ⟨h4, h6⟩
      simp [conclusion_zeckendorf_resolution_lock_m6_stable_indices] at h4 h6
      omega

end Omega.Conclusion
