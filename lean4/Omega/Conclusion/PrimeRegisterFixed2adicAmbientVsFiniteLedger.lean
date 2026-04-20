import Mathlib

namespace Omega.Conclusion

/-- The fixed rank-two ambient used to model the two-adic address space. -/
abbrev PrimeRegisterTwoAdicAmbient := Fin 2 → ℤ

/-- The canonical affine action on the fixed rank-two ambient: the two coordinates record the
translation part of the semidirect element. -/
def primeRegisterAffineAction (rk : ℕ × ℕ) :
    PrimeRegisterTwoAdicAmbient → PrimeRegisterTwoAdicAmbient :=
  fun x => ![x 0 + rk.1, x 1 + rk.2]

private theorem primeRegisterAffineAction_injective :
    Function.Injective primeRegisterAffineAction := by
  intro a b h
  have h0 : (a.1 : ℤ) = b.1 := by
    simpa [primeRegisterAffineAction] using congrArg (fun f => f (fun _ => 0) 0) h
  have h1 : (a.2 : ℤ) = b.2 := by
    simpa [primeRegisterAffineAction] using congrArg (fun f => f (fun _ => 0) 1) h
  exact Prod.ext (Int.ofNat.inj h0) (Int.ofNat.inj h1)

private theorem additiveLedger_pow (f : ℕ → ℕ) (h1 : f 1 = 0)
    (hmul : ∀ m n, f (m * n) = f m + f n) (m n : ℕ) :
    f (m ^ n) = n * f m := by
  induction n with
  | zero =>
      simp [h1]
  | succ n ih =>
      rw [pow_succ, hmul, ih, Nat.succ_mul]

private theorem two_pow_mod_two_eq_zero {n : ℕ} (hn : 0 < n) : 2 ^ n % 2 = 0 := by
  cases n with
  | zero =>
      cases Nat.lt_irrefl 0 hn
  | succ n =>
      simp [pow_succ, Nat.mul_mod]

private theorem three_pow_mod_two_eq_one (n : ℕ) : 3 ^ n % 2 = 1 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simpa [pow_succ, Nat.mul_mod, ih]

/-- A multiplicative encoding into a single additive register can never be faithful: the images of
`2` and `3` force a collision between powers of `2` and powers of `3`. -/
theorem no_faithful_single_register_additive_ledger (f : ℕ → ℕ) (h1 : f 1 = 0)
    (hmul : ∀ m n, f (m * n) = f m + f n) : ¬ Function.Injective f := by
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
    rw [additiveLedger_pow f h1 hmul 2 (f 3), additiveLedger_pow f h1 hmul 3 (f 2),
      Nat.mul_comm]
  have hcollision : 2 ^ f 3 = 3 ^ f 2 := hinj hpow_eq
  have hmod := congrArg (fun n => n % 2) hcollision
  change 2 ^ f 3 % 2 = 3 ^ f 2 % 2 at hmod
  rw [two_pow_mod_two_eq_zero hf3_pos, three_pow_mod_two_eq_one (f 2)] at hmod
  norm_num at hmod

/-- A fixed rank-two ambient already carries a faithful affine action of the prime-register model,
while a single finite additive ledger cannot faithfully realize multiplicative semantics.
    thm:conclusion-prime-register-fixed-2adic-ambient-vs-finite-ledger -/
theorem paper_conclusion_prime_register_fixed_2adic_ambient_vs_finite_ledger :
    Fintype.card (Fin 2) = 2 ∧
      Function.Injective primeRegisterAffineAction ∧
      ∀ f : ℕ → ℕ, f 1 = 0 → (∀ m n, f (m * n) = f m + f n) → ¬ Function.Injective f := by
  refine ⟨by decide, primeRegisterAffineAction_injective, ?_⟩
  intro f h1 hmul
  exact no_faithful_single_register_additive_ledger f h1 hmul

end Omega.Conclusion
