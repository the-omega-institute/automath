import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-resonance-window-forced-ramification-primes`. -/
theorem paper_conclusion_resonance_window_forced_ramification_primes
    (d : ℕ → ℕ) (disc : ℕ → ℤ) (notSquarefreeMod : ℕ → ℕ → Prop)
    (hd : ∀ q, 9 ≤ q → q ≤ 17 → 2 ≤ d q)
    (h2 : ∀ q, 9 ≤ q → q ≤ 17 → (2 : ℤ) ^ (d q - 1) ∣ disc q)
    (h3 : (3 : ℤ) ^ 8 ∣ disc 13 ∧ (3 : ℤ) ^ 8 ∣ disc 15)
    (hdisc : ∀ q p, Nat.Prime p → (p : ℤ) ∣ disc q → notSquarefreeMod q p) :
    (∀ q, 9 ≤ q → q ≤ 17 → notSquarefreeMod q 2) ∧
      notSquarefreeMod 13 3 ∧ notSquarefreeMod 15 3 := by
  constructor
  · intro q hq9 hq17
    have hExp : 1 ≤ d q - 1 := by
      have hdq : 2 ≤ d q := hd q hq9 hq17
      omega
    have hpow : (2 : ℤ) ^ 1 ∣ disc q :=
      dvd_trans (pow_dvd_pow (2 : ℤ) hExp) (h2 q hq9 hq17)
    exact hdisc q 2 Nat.prime_two (by simpa using hpow)
  · constructor
    · have hpow : (3 : ℤ) ^ 1 ∣ disc 13 :=
        dvd_trans (pow_dvd_pow (3 : ℤ) (by norm_num : 1 ≤ 8)) h3.1
      exact hdisc 13 3 Nat.prime_three (by simpa using hpow)
    · have hpow : (3 : ℤ) ^ 1 ∣ disc 15 :=
        dvd_trans (pow_dvd_pow (3 : ℤ) (by norm_num : 1 ≤ 8)) h3.2
      exact hdisc 15 3 Nat.prime_three (by simpa using hpow)

end Omega.Conclusion
