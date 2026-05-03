import Mathlib.Data.Nat.Prime.Basic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-phase-cover-prime-ledger-support-union`.
The prime support of a product is the union of the prime supports of the factors. -/
theorem paper_conclusion_phase_cover_prime_ledger_support_union (detA detB : ℕ) :
    {p : ℕ | Nat.Prime p ∧ p ∣ detA * detB} =
      {p : ℕ | Nat.Prime p ∧ p ∣ detA} ∪ {p : ℕ | Nat.Prime p ∧ p ∣ detB} := by
  ext p
  constructor
  · intro hp_prod
    rcases hp_prod with ⟨hp_prime, hp_dvd_prod⟩
    rcases hp_prime.dvd_mul.mp hp_dvd_prod with hp_dvd_A | hp_dvd_B
    · exact Or.inl ⟨hp_prime, hp_dvd_A⟩
    · exact Or.inr ⟨hp_prime, hp_dvd_B⟩
  · intro hp_union
    rcases hp_union with hp_A | hp_B
    · exact ⟨hp_A.1, dvd_mul_of_dvd_left hp_A.2 detB⟩
    · exact ⟨hp_B.1, dvd_mul_of_dvd_right hp_B.2 detA⟩

end Omega.Conclusion
