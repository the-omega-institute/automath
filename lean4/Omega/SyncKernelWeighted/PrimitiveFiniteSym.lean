import Mathlib
import Omega.SyncKernelWeighted.TraceCentralMomentsZero

open scoped BigOperators

namespace Omega.SyncKernelWeighted

/-- Total mass of the finite primitive profile on `{0, …, n}`. -/
def primitiveFiniteMass (n : ℕ) (a : ℕ → ℚ) : ℚ :=
  Finset.sum (Finset.range (n + 1)) a

/-- Normalized mean of the finite primitive profile. -/
def primitiveFiniteMean (n : ℕ) (a : ℕ → ℚ) : ℚ :=
  (Finset.sum (Finset.range (n + 1)) fun k => (k : ℚ) * a k) / primitiveFiniteMass n a

/-- Normalized odd centered moment of the finite primitive profile. -/
def primitiveFiniteOddCenteredMoment (n m : ℕ) (a : ℕ → ℚ) : ℚ :=
  (Finset.sum (Finset.range (n + 1))
      fun k => (((k : ℚ) - (n : ℚ) / 2) ^ (2 * m + 1)) * a k) /
    primitiveFiniteMass n a

/-- Paper label: `cor:primitive-finite-sym`.
Finite palindromic primitive profiles have mean `n / 2`, and every odd centered moment vanishes. -/
theorem paper_primitive_finite_sym (n m : ℕ) (a : ℕ → ℚ)
    (hpal : ∀ k, k ≤ n → a k = a (n - k))
    (hmass : primitiveFiniteMass n a ≠ 0) :
    primitiveFiniteMean n a = (n : ℚ) / 2 ∧ primitiveFiniteOddCenteredMoment n m a = 0 := by
  have hcenter0 := paper_trace_central_moments_zero n 0 a hpal
  have hmean_num :
      Finset.sum (Finset.range (n + 1)) (fun k => (k : ℚ) * a k) =
        (n : ℚ) / 2 * primitiveFiniteMass n a := by
    have hcenter :
        Finset.sum (Finset.range (n + 1)) (fun k => ((k : ℚ) - (n : ℚ) / 2) * a k) = 0 := by
      simpa [pow_one, mul_comm] using hcenter0
    have hsplit :
        Finset.sum (Finset.range (n + 1)) (fun k => ((k : ℚ) - (n : ℚ) / 2) * a k) =
          Finset.sum (Finset.range (n + 1)) (fun k => (k : ℚ) * a k) -
            (n : ℚ) / 2 * primitiveFiniteMass n a := by
      calc
        Finset.sum (Finset.range (n + 1)) (fun k => ((k : ℚ) - (n : ℚ) / 2) * a k) =
            Finset.sum (Finset.range (n + 1))
              (fun k => (k : ℚ) * a k - ((n : ℚ) / 2) * a k) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              ring
        _ =
            Finset.sum (Finset.range (n + 1)) (fun k => (k : ℚ) * a k) -
              Finset.sum (Finset.range (n + 1)) (fun k => ((n : ℚ) / 2) * a k) := by
              rw [Finset.sum_sub_distrib]
        _ =
            Finset.sum (Finset.range (n + 1)) (fun k => (k : ℚ) * a k) -
              primitiveFiniteMass n a * ((n : ℚ) / 2) := by
              simp [primitiveFiniteMass, Finset.sum_mul, mul_comm]
        _ =
            Finset.sum (Finset.range (n + 1)) (fun k => (k : ℚ) * a k) -
              (n : ℚ) / 2 * primitiveFiniteMass n a := by
              ring
    rw [hsplit] at hcenter
    exact sub_eq_zero.mp hcenter
  have hodd_num := paper_trace_central_moments_zero n m a hpal
  constructor
  · unfold primitiveFiniteMean
    exact (div_eq_iff hmass).2 hmean_num
  · unfold primitiveFiniteOddCenteredMoment
    exact (div_eq_iff hmass).2 (by simpa [primitiveFiniteMass] using hodd_num)

end Omega.SyncKernelWeighted
