import Mathlib.Data.Nat.Basic

theorem paper_xi_time_part63b_infinite_depth_finite_prime_register_impossibility
    (available : ℕ) (needed : ℕ → ℕ) (hneeded : ∀ k : ℕ, 1 ≤ k → k ≤ needed k) :
    ¬ (∀ k : ℕ, 1 ≤ k → needed k ≤ available) := by
  intro hbudget
  have hkpos : 1 ≤ available + 1 := Nat.succ_le_succ (Nat.zero_le available)
  have hlower : available + 1 ≤ needed (available + 1) :=
    hneeded (available + 1) hkpos
  have hupper : needed (available + 1) ≤ available := hbudget (available + 1) hkpos
  have hcontr : available.succ ≤ available := by
    simpa [Nat.succ_eq_add_one] using Nat.le_trans hlower hupper
  exact Nat.not_succ_le_self available hcontr
