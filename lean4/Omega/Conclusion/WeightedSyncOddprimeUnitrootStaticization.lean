import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-weighted-sync-oddprime-unitroot-staticization`. -/
theorem paper_conclusion_weighted_sync_oddprime_unitroot_staticization
    (p : ℕ) (a : ℕ → ℤ) (A : ℤ) (hprime : Nat.Prime p) (hodd : p ≠ 2)
    (htail : ∀ k : ℕ, (p : ℤ) ^ (k + 1) ∣ A - a (p ^ k)) (hself : A = -A) :
    (∀ ℓ k : ℕ, 1 ≤ ℓ → ℓ ≤ k + 1 → (p : ℤ) ^ ℓ ∣ A - a (p ^ k)) ∧
      A = 0 := by
  have _hprime : Nat.Prime p := hprime
  have _hodd : p ≠ 2 := hodd
  constructor
  · intro ℓ k _hℓ hℓk
    exact dvd_trans (pow_dvd_pow (p : ℤ) hℓk) (htail k)
  · omega

end Omega.Conclusion
