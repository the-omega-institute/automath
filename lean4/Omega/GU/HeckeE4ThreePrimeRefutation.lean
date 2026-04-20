import Mathlib.Tactic

namespace Omega.GU

/-- Instantiating the weight-`4` Eisenstein coefficient formula at the first three audit primes
produces the concrete finite refutation certificate.
    cor:hecke-e4-three-prime-refutation -/
theorem paper_hecke_e4_three_prime_refutation
    (a : ℕ → ℤ) (hE4 : ∀ p : ℕ, Nat.Prime p → a p = 240 * (1 + p ^ 3)) :
    a 2 = 2160 ∧ a 3 = 6720 ∧ a 5 = 30240 := by
  have h2 : a 2 = 2160 := by
    have h := hE4 2 Nat.prime_two
    norm_num at h ⊢
    exact h
  have h3 : a 3 = 6720 := by
    have h := hE4 3 Nat.prime_three
    norm_num at h ⊢
    exact h
  have h5 : a 5 = 30240 := by
    have h := hE4 5 (by norm_num : Nat.Prime 5)
    norm_num at h ⊢
    exact h
  exact ⟨h2, h3, h5⟩

end Omega.GU
