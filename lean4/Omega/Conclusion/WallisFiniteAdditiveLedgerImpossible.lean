import Mathlib.Tactic

namespace Omega.Conclusion

/-- A faithful finite additive ledger for the Wallis multiplicative skeleton. -/
def conclusion_wallis_finite_additive_ledger_impossible_hasFiniteAdditiveLinearization : Prop :=
  ∃ f : ℕ → ℕ, f 1 = 0 ∧ (∀ m n, f (m * n) = f m + f n) ∧ Function.Injective f

lemma conclusion_wallis_finite_additive_ledger_impossible_factor_cover
    (m : ℕ) (hm : 0 < m) :
    (∃ n : ℕ, 0 < n ∧ m = 2 * n) ∨
      (∃ n : ℕ, 0 < n ∧ m = 2 * n - 1) ∨
      (∃ n : ℕ, 0 < n ∧ m = 2 * n + 1) := by
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · left
    exact ⟨k, by omega, by omega⟩
  · by_cases hk0 : k = 0
    · right
      left
      exact ⟨1, by omega, by omega⟩
    · right
      right
      exact ⟨k, by omega, by omega⟩

lemma conclusion_wallis_finite_additive_ledger_impossible_additiveLedger_pow
    (f : ℕ → ℕ) (h1 : f 1 = 0) (hmul : ∀ m n, f (m * n) = f m + f n) (m n : ℕ) :
    f (m ^ n) = n * f m := by
  induction n with
  | zero =>
      simp [h1]
  | succ n ih =>
      rw [pow_succ, hmul, ih, Nat.succ_mul]

lemma conclusion_wallis_finite_additive_ledger_impossible_two_pow_mod_two_eq_zero
    {n : ℕ} (hn : 0 < n) : 2 ^ n % 2 = 0 := by
  cases n with
  | zero =>
      cases Nat.lt_irrefl 0 hn
  | succ n =>
      simp [pow_succ]

lemma conclusion_wallis_finite_additive_ledger_impossible_three_pow_mod_two_eq_one
    (n : ℕ) : 3 ^ n % 2 = 1 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simp [pow_succ, Nat.mul_mod, ih]

lemma conclusion_wallis_finite_additive_ledger_impossible_no_faithful_additive_ledger
    (f : ℕ → ℕ) (h1 : f 1 = 0) (hmul : ∀ m n, f (m * n) = f m + f n) :
    ¬ Function.Injective f := by
  intro hinj
  have hf2_ne : f 2 ≠ 0 := by
    intro hf2
    have h21 : 2 = 1 := hinj (hf2.trans h1.symm)
    norm_num at h21
  have hf3_ne : f 3 ≠ 0 := by
    intro hf3
    have h31 : 3 = 1 := hinj (hf3.trans h1.symm)
    norm_num at h31
  have hf2_pos : 0 < f 2 := Nat.pos_of_ne_zero hf2_ne
  have hf3_pos : 0 < f 3 := Nat.pos_of_ne_zero hf3_ne
  have hpow_eq : f (2 ^ f 3) = f (3 ^ f 2) := by
    rw [conclusion_wallis_finite_additive_ledger_impossible_additiveLedger_pow f h1 hmul 2 (f 3),
      conclusion_wallis_finite_additive_ledger_impossible_additiveLedger_pow f h1 hmul 3 (f 2),
      Nat.mul_comm]
  have hcollision : 2 ^ f 3 = 3 ^ f 2 := hinj hpow_eq
  have hmod := congrArg (fun n => n % 2) hcollision
  change 2 ^ f 3 % 2 = 3 ^ f 2 % 2 at hmod
  rw [conclusion_wallis_finite_additive_ledger_impossible_two_pow_mod_two_eq_zero hf3_pos,
    conclusion_wallis_finite_additive_ledger_impossible_three_pow_mod_two_eq_one (f 2)] at hmod
  norm_num at hmod

/-- Concrete Wallis-channel formulation: the Wallis factor generators already cover every positive
integer, and therefore no faithful finite additive ledger can linearize the induced multiplicative
skeleton. -/
def conclusion_wallis_finite_additive_ledger_impossible_statement : Prop :=
  (∀ m : ℕ, 0 < m →
      (∃ n, 0 < n ∧ m = 2 * n) ∨
        (∃ n, 0 < n ∧ m = 2 * n - 1) ∨
        (∃ n, 0 < n ∧ m = 2 * n + 1)) ∧
    ¬ conclusion_wallis_finite_additive_ledger_impossible_hasFiniteAdditiveLinearization

/-- Paper label: `thm:conclusion-wallis-finite-additive-ledger-impossible`. The Wallis factor
monoid is already the full positive multiplicative semigroup, and the standard power-collision
argument shows that no finite additive ledger can remain faithful on it. -/
theorem paper_conclusion_wallis_finite_additive_ledger_impossible :
    conclusion_wallis_finite_additive_ledger_impossible_statement := by
  refine ⟨fun m hm => conclusion_wallis_finite_additive_ledger_impossible_factor_cover m hm, ?_⟩
  rintro ⟨f, h1, hmul, hinj⟩
  exact conclusion_wallis_finite_additive_ledger_impossible_no_faithful_additive_ledger
    f h1 hmul hinj

end Omega.Conclusion
