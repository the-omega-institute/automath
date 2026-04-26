import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-prime-modulus-exception-scheme-collapse`. -/
theorem paper_conclusion_prime_modulus_exception_scheme_collapse (badModulus : ℕ -> Prop)
    (p0 : ℕ)
    (hCofinal : forall p, Nat.Prime p -> p != 2 -> p0 <= p -> badModulus p) :
    ¬ ∃ S : Finset ℕ, forall p, Nat.Prime p -> p ∉ S -> ¬ badModulus p := by
  intro hFinite
  rcases hFinite with ⟨S, hS⟩
  obtain ⟨p, hpLarge, hpPrime⟩ := Nat.exists_infinite_primes (max p0 (max 3 (S.sup id + 1)))
  have hp0 : p0 ≤ p := le_trans (le_max_left _ _) hpLarge
  have hpThreshold : max 3 (S.sup id + 1) ≤ p := le_trans (le_max_right _ _) hpLarge
  have hpGeThree : 3 ≤ p := le_trans (le_max_left _ _) hpThreshold
  have hpNeTwo : p ≠ 2 := by omega
  have hpNotMem : p ∉ S := by
    intro hpMem
    have hpLeSup : p ≤ S.sup id := by
      simpa using (Finset.le_sup (f := id) hpMem)
    omega
  have hpBad : badModulus p := hCofinal p hpPrime (by simp [hpNeTwo]) hp0
  exact (hS p hpPrime hpNotMem) hpBad

end Omega.Conclusion
