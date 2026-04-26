import Omega.POM.MultiplicityFixedLREnvelope

namespace Omega.POM.MultiplicityFixedRExtrema

open Nat

/-- Fibonacci triple identity: `3·fib(n+2) = fib(n+4) + fib n`.
    prop:pom-multiplicity-fixed-r-extrema -/
theorem fib_three_mul (n : ℕ) :
    3 * fib (n + 2) = fib (n + 4) + fib n := by
  have h2 : fib (n + 2) = fib n + fib (n + 1) := fib_add_two
  have h3 : fib (n + 3) = fib (n + 1) + fib (n + 2) := fib_add_two
  have h4 : fib (n + 4) = fib (n + 2) + fib (n + 3) := fib_add_two
  rw [h4, h3, h2]
  ring

/-- `2·fib(n+4) = 3·fib(n+3) + fib n`.
    prop:pom-multiplicity-fixed-r-extrema -/
theorem two_fib_add_four_eq_three_fib_add_three_plus_fib (n : ℕ) :
    2 * fib (n + 4) = 3 * fib (n + 3) + fib n := by
  have h2 : fib (n + 2) = fib n + fib (n + 1) := fib_add_two
  have h3 : fib (n + 3) = fib (n + 1) + fib (n + 2) := fib_add_two
  have h4 : fib (n + 4) = fib (n + 2) + fib (n + 3) := fib_add_two
  rw [h4, h3, h2]
  ring

/-- Mathlib form: `fib(m+n+1) = fib m · fib n + fib(m+1) · fib(n+1)`.
    prop:pom-multiplicity-fixed-r-extrema -/
theorem fib_add_one_eq_mul_add_mul (m n : ℕ) :
    fib (m + n + 1) = fib m * fib n + fib (m + 1) * fib (n + 1) :=
  Nat.fib_add m n

/-- Shifted fusion: `fib(a+2)·fib(b+2) + fib(a+1)·fib(b+1) = fib(a+b+3)`.
    (Direct from `fib_add` applied to `(a+1)+(b+1)+1 = a+b+3`.)
    prop:pom-multiplicity-fixed-r-extrema -/
theorem fib_shifted_fusion (a b : ℕ) :
    fib (a + 2) * fib (b + 2) + fib (a + 1) * fib (b + 1) = fib (a + b + 3) := by
  have h : fib ((a + 1) + (b + 1) + 1) =
      fib (a + 1) * fib (b + 1) + fib (a + 1 + 1) * fib (b + 1 + 1) := Nat.fib_add (a+1) (b+1)
  have heq : (a + 1) + (b + 1) + 1 = a + b + 3 := by omega
  have h2a : a + 1 + 1 = a + 2 := by omega
  have h2b : b + 1 + 1 = b + 2 := by omega
  rw [heq, h2a, h2b] at h
  omega

/-- `2·fib(a+b+3) = fib(a+3)·fib(b+3) + fib(a+1)·fib(b+1)`
    (partial algebraic identity; uses `fib_add` at `(a+2),(b+2)`).
    prop:pom-multiplicity-fixed-r-extrema -/
theorem fib_shifted_fusion_five (a b : ℕ) :
    fib (a + 2) * fib (b + 2) + fib (a + 3) * fib (b + 3) = fib (a + b + 5) := by
  have h : fib ((a + 2) + (b + 2) + 1) =
      fib (a + 2) * fib (b + 2) + fib (a + 2 + 1) * fib (b + 2 + 1) := Nat.fib_add (a+2) (b+2)
  have heq : (a + 2) + (b + 2) + 1 = a + b + 5 := by omega
  have ha : a + 2 + 1 = a + 3 := by omega
  have hb : b + 2 + 1 = b + 3 := by omega
  rw [heq, ha, hb] at h
  omega

/-- Strict lower bound: `fib(a+3)·fib(b+3) < 2·fib(a+b+5)` for `a,b ≥ 0`
    (using that `fib(a+2),fib(b+2) ≥ 1`).
    prop:pom-multiplicity-fixed-r-extrema -/
theorem two_fib_gt_fib_mul_fib (a b : ℕ) :
    fib (a + 3) * fib (b + 3) < 2 * fib (a + b + 5) := by
  have h := fib_shifted_fusion_five a b
  have ha : 0 < fib (a + 2) := Nat.fib_pos.mpr (by omega)
  have hb : 0 < fib (b + 2) := Nat.fib_pos.mpr (by omega)
  have hprod : 0 < fib (a + 2) * fib (b + 2) := Nat.mul_pos ha hb
  omega

/-- Strict lower bound: `3·fib(n+3) < 2·fib(n+4)` for `n ≥ 1`.
    prop:pom-multiplicity-fixed-r-extrema -/
theorem two_fib_gt_three_fib (n : ℕ) (hn : 1 ≤ n) :
    3 * fib (n + 3) < 2 * fib (n + 4) := by
  have h := two_fib_add_four_eq_three_fib_add_three_plus_fib n
  have hpos : 0 < fib n := Nat.fib_pos.mpr hn
  omega

/-- Paper package: algebraic core of multiplicity-fixed-r extrema.
    prop:pom-multiplicity-fixed-r-extrema -/
theorem paper_pom_multiplicity_fixed_r_extrema_algebra_core :
    (∀ n : ℕ, 3 * fib (n + 2) = fib (n + 4) + fib n) ∧
    (∀ n : ℕ, 2 * fib (n + 4) = 3 * fib (n + 3) + fib n) ∧
    (∀ a b : ℕ,
      fib (a + 2) * fib (b + 2) + fib (a + 1) * fib (b + 1) = fib (a + b + 3)) :=
  ⟨fib_three_mul,
   two_fib_add_four_eq_three_fib_add_three_plus_fib,
   fib_shifted_fusion⟩

/-- Paper wrapper for the fixed-`(L,r)` multiplicity extremal witnesses and closed-form
    endpoint values proved in the shared envelope module.
    prop:pom-multiplicity-fixed-r-extrema -/
theorem paper_pom_multiplicity_fixed_r_extrema (L r : ℕ) (_hL : 1 ≤ L) (hr : 1 ≤ r) (hrL : r ≤ L) :
    Omega.POM.multiplicityFixedLREnvelopeStatement L r :=
  Omega.POM.paper_pom_multiplicity_fixed_L_r_envelope L r (by omega) hr hrL

end Omega.POM.MultiplicityFixedRExtrema
