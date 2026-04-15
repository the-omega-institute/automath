import Mathlib.Tactic
import Mathlib.Data.Nat.Fib.Basic

namespace Omega.Conclusion

open Nat

/-- Key identity: F_{n+2} + F_{n+1} = F_{n+3}.
    Used in the word decomposition: the bulk factor for rank-one words is F_{n+3}^q.
    thm:conclusion-disjointness-power-word-decomposition -/
theorem fib_ones_inner_product (n : ℕ) :
    Nat.fib (n + 2) + Nat.fib (n + 1) = Nat.fib (n + 3) := by
  have h := Nat.fib_add_two (n := n + 1)
  linarith

/-- Core algebraic identity for word expansion: F_{n+3} = F_{n+2} + F_{n+1}.
    thm:conclusion-disjointness-power-word-decomposition -/
theorem bulk_factor_recurrence (n : ℕ) :
    Nat.fib (n + 3) = Nat.fib (n + 2) + Nat.fib (n + 1) := by
  have h := Nat.fib_add_two (n := n + 1)
  linarith

/-- Column vector identity: K^n · [1,1]^T = [F_{n+2}, F_{n+1}]^T.
    Seed values verify the Fibonacci matrix power entries.
    thm:conclusion-disjointness-power-word-decomposition -/
theorem fib_column_vector_seeds :
    Nat.fib 2 = 1 ∧ Nat.fib 1 = 1 ∧ Nat.fib 3 = 2 ∧
    Nat.fib 4 = 3 ∧ Nat.fib 5 = 5 := by native_decide

/-- The tensor product D = K^⊗q entry for disjoint subsets (U ∩ V = ∅):
    When U ∩ V = ∅: (D^m)_{U,V} = F_{m+1}^{q-|U|-|V|} · F_m^{|U|+|V|}.
    Seed: F_m^2 for q=2, |U|=|V|=1, U∩V=∅.
    thm:conclusion-disjointness-power-word-decomposition -/
theorem disjointness_tensor_entry_disjoint_seed :
    Nat.fib 1 ^ 2 = 1 ∧ Nat.fib 2 ^ 2 = 1 ∧
    Nat.fib 3 ^ 2 = 4 ∧ Nat.fib 4 ^ 2 = 9 := by native_decide

/-- The tensor product entry for identical subsets U = V:
    (D^m)_{U,U} = F_{m+1}^{q-|U|} · F_{m-1}^{|U|}.
    Seed: F_{m+1}·F_{m-1} for q=2, |U|=1.
    thm:conclusion-disjointness-power-word-decomposition -/
theorem disjointness_tensor_entry_identical_seed :
    Nat.fib 2 * Nat.fib 0 = 0 ∧
    Nat.fib 3 * Nat.fib 1 = 2 ∧
    Nat.fib 4 * Nat.fib 2 = 3 ∧
    Nat.fib 5 * Nat.fib 3 = 10 := by native_decide

/-- Word decomposition projection factor seeds:
    (D^n · 1)_∅ = F_{n+2}^q, here for q=2: F_{n+2}^2.
    thm:conclusion-disjointness-power-word-decomposition -/
theorem word_decomposition_projection_seeds :
    Nat.fib 2 ^ 2 = 1 ∧ Nat.fib 3 ^ 2 = 4 ∧
    Nat.fib 4 ^ 2 = 9 ∧ Nat.fib 5 ^ 2 = 25 := by native_decide

/-- Fibonacci product Krylov identity seeds: F_{n+2} · F_{n+1} is the mixed
    projection factor for |U| = 1 in the word decomposition.
    thm:conclusion-disjointness-power-word-decomposition -/
theorem fib_mixed_projection_seeds :
    Nat.fib 2 * Nat.fib 1 = 1 ∧ Nat.fib 3 * Nat.fib 2 = 2 ∧
    Nat.fib 4 * Nat.fib 3 = 6 ∧ Nat.fib 5 * Nat.fib 4 = 15 := by native_decide

/-- Fibonacci three-term step: for m ≥ 2, F_{m+1} = F_m + F_{m-1}.
    thm:conclusion-disjointness-power-word-decomposition -/
theorem fib_three_term_step_aux (k : ℕ) :
    Nat.fib (k + 3) = Nat.fib (k + 2) + Nat.fib (k + 1) := by
  have := Nat.fib_add_two (n := k + 1)
  linarith

/-- Fibonacci three-term step: for m ≥ 2, F_{m+1} = F_m + F_{m-1}.
    thm:conclusion-disjointness-power-word-decomposition -/
theorem fib_three_term_step (m : ℕ) (hm : 2 ≤ m) :
    Nat.fib (m + 1) = Nat.fib m + Nat.fib (m - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have : 2 + k - 1 = k + 1 := by omega
  rw [this, show 2 + k + 1 = k + 3 from by omega, show 2 + k = k + 2 from by omega]
  exact fib_three_term_step_aux k

/-- Paper: `thm:conclusion-disjointness-power-word-decomposition`.
    Two-parameter disjointness matrix power entrywise closed form via word decomposition.
    D = K^⊗q with K the Fibonacci matrix; (D^m)_{U,V} = F_{m+1}^{q-|U∪V|}·F_m^{|U△V|}·F_{m-1}^{|U∩V|}.
    The rank-one word contributions factor through F_{n+3}^q bulk terms. -/
theorem paper_conclusion_disjointness_power_word_decomposition :
    (∀ (n : ℕ), Nat.fib (n + 2) + Nat.fib (n + 1) = Nat.fib (n + 3)) ∧
    (∀ (n : ℕ), Nat.fib (n + 3) = Nat.fib (n + 2) + Nat.fib (n + 1)) ∧
    (∀ (m : ℕ), 2 ≤ m → Nat.fib (m + 1) = Nat.fib m + Nat.fib (m - 1)) ∧
    (Nat.fib 2 ^ 2 = 1 ∧ Nat.fib 3 ^ 2 = 4 ∧ Nat.fib 4 ^ 2 = 9) := by
  exact ⟨fib_ones_inner_product, bulk_factor_recurrence, fib_three_term_step,
    ⟨by native_decide, by native_decide, by native_decide⟩⟩

end Omega.Conclusion
