import Mathlib.Data.Nat.Factorization.Basic
import Omega.POM.FiberMultiplicityV2Thresholds

namespace Omega.POM

/-- The shifted-Fibonacci product giving the component-factorized fiber multiplicity. -/
def pom_fiber_multiplicity_linear_2adic_divisibility_multiplicity
    (lengths : List ℕ) : ℕ :=
  (lengths.map fun ell => Nat.fib (ell + 2)).prod

/-- Components in the Pisano-`1` class modulo `3`, i.e. exactly the components whose
shifted-Fibonacci factor is even. -/
def pom_fiber_multiplicity_linear_2adic_divisibility_pisanoOneCount
    (lengths : List ℕ) : ℕ :=
  (lengths.filter fun ell => ell % 3 = 1).length

private lemma pom_fiber_multiplicity_linear_2adic_divisibility_one_le_factorization
    {ell : ℕ} (hell : ell % 3 = 1) :
    1 ≤ (Nat.fib (ell + 2)).factorization 2 := by
  have hnotOdd : ¬ Odd (Nat.fib (ell + 2)) := by
    rw [pom_fiber_multiplicity_v2_thresholds_fib_add_two_odd_iff]
    exact not_not.mpr hell
  have hEven : Even (Nat.fib (ell + 2)) := Nat.not_odd_iff_even.mp hnotOdd
  have hdvd : 2 ∣ Nat.fib (ell + 2) := by
    rwa [even_iff_two_dvd] at hEven
  exact (Nat.prime_two.dvd_iff_one_le_factorization
    (pom_fiber_multiplicity_v2_thresholds_fib_ne_zero ell)).mp hdvd

private lemma pom_fiber_multiplicity_linear_2adic_divisibility_count_le_sum
    (lengths : List ℕ) :
    pom_fiber_multiplicity_linear_2adic_divisibility_pisanoOneCount lengths ≤
      (lengths.map (fun ell => (Nat.fib (ell + 2)).factorization 2)).sum := by
  induction lengths with
  | nil =>
      simp [pom_fiber_multiplicity_linear_2adic_divisibility_pisanoOneCount]
  | cons ell rest ih =>
      have ih' :
          (rest.filter fun ell => ell % 3 = 1).length ≤
            (rest.map (fun ell => (Nat.fib (ell + 2)).factorization 2)).sum := by
        simpa [pom_fiber_multiplicity_linear_2adic_divisibility_pisanoOneCount] using ih
      by_cases hell : ell % 3 = 1
      · have hfactor :=
          pom_fiber_multiplicity_linear_2adic_divisibility_one_le_factorization hell
        simp [pom_fiber_multiplicity_linear_2adic_divisibility_pisanoOneCount, hell]
        omega
      · simp [pom_fiber_multiplicity_linear_2adic_divisibility_pisanoOneCount, hell]
        exact Nat.le_trans ih' (Nat.le_add_left _ _)

/-- Concrete statement for `cor:pom-fiber-multiplicity-linear-2adic-divisibility`: the
`2`-adic valuation of the shifted-Fibonacci product is at least the number of components in the
Pisano-`1` class, and hence its lower-tail event is contained in the corresponding component-count
lower-tail event. -/
def pom_fiber_multiplicity_linear_2adic_divisibility_statement : Prop :=
  ∀ (lengths : List ℕ) (threshold : ℕ),
    pom_fiber_multiplicity_linear_2adic_divisibility_pisanoOneCount lengths ≤
        (pom_fiber_multiplicity_linear_2adic_divisibility_multiplicity lengths).factorization 2 ∧
      ((pom_fiber_multiplicity_linear_2adic_divisibility_multiplicity lengths).factorization 2 ≤
          threshold →
        pom_fiber_multiplicity_linear_2adic_divisibility_pisanoOneCount lengths ≤ threshold)

/-- Paper label: `cor:pom-fiber-multiplicity-linear-2adic-divisibility`. -/
theorem paper_pom_fiber_multiplicity_linear_2adic_divisibility :
    pom_fiber_multiplicity_linear_2adic_divisibility_statement := by
  intro lengths threshold
  have hfac :
      (pom_fiber_multiplicity_linear_2adic_divisibility_multiplicity lengths).factorization 2 =
        (lengths.map (fun ell => (Nat.fib (ell + 2)).factorization 2)).sum := by
    simpa [pom_fiber_multiplicity_linear_2adic_divisibility_multiplicity] using
      pom_fiber_multiplicity_v2_thresholds_factorization_prod lengths
  have hcount :
      pom_fiber_multiplicity_linear_2adic_divisibility_pisanoOneCount lengths ≤
        (pom_fiber_multiplicity_linear_2adic_divisibility_multiplicity lengths).factorization 2 := by
    rw [hfac]
    exact pom_fiber_multiplicity_linear_2adic_divisibility_count_le_sum lengths
  exact ⟨hcount, fun htail => Nat.le_trans hcount htail⟩

end Omega.POM
