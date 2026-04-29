import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-gramshift-padic-effective-precision`. -/
theorem paper_xi_gramshift_padic_effective_precision {κ p N s : ℕ}
    {A A' Num Num' : Fin κ → Fin κ → ℤ} (hsN : s ≤ N)
    (hNum : ∀ i j, (p ^ N : ℤ) ∣ Num i j - Num' i j)
    (hA : ∀ i j, (p ^ s : ℤ) * A i j = Num i j)
    (hA' : ∀ i j, (p ^ s : ℤ) * A' i j = Num' i j)
    (hcancel : ∀ z : ℤ, (p ^ N : ℤ) ∣ (p ^ s : ℤ) * z →
      (p ^ (N - s) : ℤ) ∣ z) :
    ∀ i j, (p ^ (N - s) : ℤ) ∣ A i j - A' i j := by
  intro i j
  have _hsN := hsN
  apply hcancel
  have h := hNum i j
  rw [← hA i j, ← hA' i j] at h
  convert h using 1
  ring

end Omega.Zeta
