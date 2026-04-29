import Mathlib.Tactic

namespace Omega.POM.TorsionSymmetryCoprimeClosure

/-- If a sequence is supported only on multiples of two coprime moduli, it is supported only
on multiples of their product.
    cor:pom-torsion-symmetry-coprime-closure -/
theorem paper_pom_torsion_symmetry_coprime_closure {R : Type*} [Zero R] (u : ℕ → R)
    (q1 q2 : ℕ) (hcop : Nat.Coprime q1 q2) (h1 : ∀ n, ¬ q1 ∣ n → u n = 0)
    (h2 : ∀ n, ¬ q2 ∣ n → u n = 0) :
    ∀ n, ¬ q1 * q2 ∣ n → u n = 0 := by
  intro n hn
  by_cases hq1 : q1 ∣ n
  · by_cases hq2 : q2 ∣ n
    · exact False.elim (hn (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hq1 hq2))
    · exact h2 n hq2
  · exact h1 n hq1

end Omega.POM.TorsionSymmetryCoprimeClosure
