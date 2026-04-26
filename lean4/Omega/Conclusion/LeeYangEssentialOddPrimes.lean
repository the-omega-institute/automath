import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-lee-yang-essential-odd-primes`. -/
theorem paper_conclusion_lee_yang_essential_odd_primes
    (S_ess : ℕ → Prop)
    (h_of_dvd : ∀ p : ℕ, p ∣ (3 ^ 9 * 31 ^ 2 * 37 : ℕ) → S_ess p) :
    S_ess 3 ∧ S_ess 31 ∧ S_ess 37 := by
  refine ⟨h_of_dvd 3 ?_, h_of_dvd 31 ?_, h_of_dvd 37 ?_⟩ <;> norm_num

end Omega.Conclusion
