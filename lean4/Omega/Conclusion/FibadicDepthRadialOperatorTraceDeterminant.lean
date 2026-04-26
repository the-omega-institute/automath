import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

/-- Finite zeta transform of a finitely supported gcd-radial coefficient family. -/
def conclusion_fibadic_depth_radial_operator_trace_determinant_hat
    (support : Finset ℕ) (alpha : ℕ → ℤ) (d : ℕ) : ℤ :=
  (support.filter (fun m => d ∣ m)).sum (fun m => alpha m)

/-- Trace of the finite visible layer after diagonalizing by exact-depth blocks. -/
def conclusion_fibadic_depth_radial_operator_trace_determinant_trace
    (N : ℕ) (support : Finset ℕ) (alpha : ℕ → ℤ) (multiplicity : ℕ → ℕ) : ℤ :=
  (Nat.divisors N).sum (fun d =>
    (multiplicity d : ℤ) *
      conclusion_fibadic_depth_radial_operator_trace_determinant_hat support alpha d)

/-- Determinant as the product over diagonal exact-depth blocks. -/
def conclusion_fibadic_depth_radial_operator_trace_determinant_det
    (N : ℕ) (support : Finset ℕ) (alpha : ℕ → ℤ) (multiplicity : ℕ → ℕ) : ℤ :=
  (Nat.divisors N).prod (fun d =>
    conclusion_fibadic_depth_radial_operator_trace_determinant_hat support alpha d ^
      multiplicity d)

/-- Characteristic determinant of `I - zT` over exact-depth blocks. -/
def conclusion_fibadic_depth_radial_operator_trace_determinant_char
    (N : ℕ) (support : Finset ℕ) (alpha : ℕ → ℤ) (multiplicity : ℕ → ℕ) (z : ℤ) : ℤ :=
  (Nat.divisors N).prod (fun d =>
    (1 - z * conclusion_fibadic_depth_radial_operator_trace_determinant_hat support alpha d) ^
      multiplicity d)

/-- The closed gcd-depth trace after interchanging the finite divisor and support sums. -/
def conclusion_fibadic_depth_radial_operator_trace_determinant_gcdTrace
    (N : ℕ) (support : Finset ℕ) (alpha : ℕ → ℤ) (multiplicity : ℕ → ℕ) : ℤ :=
  support.sum (fun m => alpha m *
    ((Nat.divisors N).filter (fun d => d ∣ m)).sum (fun d => (multiplicity d : ℤ)))

lemma conclusion_fibadic_depth_radial_operator_trace_determinant_trace_eq_gcdTrace
    (N : ℕ) (support : Finset ℕ) (alpha : ℕ → ℤ) (multiplicity : ℕ → ℕ) :
    conclusion_fibadic_depth_radial_operator_trace_determinant_trace N support alpha
        multiplicity =
      conclusion_fibadic_depth_radial_operator_trace_determinant_gcdTrace N support alpha
        multiplicity := by
  unfold conclusion_fibadic_depth_radial_operator_trace_determinant_trace
    conclusion_fibadic_depth_radial_operator_trace_determinant_hat
    conclusion_fibadic_depth_radial_operator_trace_determinant_gcdTrace
  calc
    ((Nat.divisors N).sum (fun d =>
        (multiplicity d : ℤ) *
          (support.filter (fun m => d ∣ m)).sum (fun m => alpha m)))
        = (Nat.divisors N).sum (fun d =>
            (support.filter (fun m => d ∣ m)).sum (fun m =>
              (multiplicity d : ℤ) * alpha m)) := by
          simp [Finset.mul_sum]
    _ = (Nat.divisors N).sum (fun d =>
          support.sum (fun m =>
            if d ∣ m then (multiplicity d : ℤ) * alpha m else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro d hd
          rw [Finset.sum_filter]
    _ = support.sum (fun m =>
          (Nat.divisors N).sum (fun d =>
            if d ∣ m then (multiplicity d : ℤ) * alpha m else 0)) := by
          rw [Finset.sum_comm]
    _ = support.sum (fun m => alpha m *
          ((Nat.divisors N).filter (fun d => d ∣ m)).sum
            (fun d => (multiplicity d : ℤ))) := by
          refine Finset.sum_congr rfl ?_
          intro m hm
          rw [Finset.sum_filter, Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro d hd
          by_cases hdm : d ∣ m <;> simp [hdm, mul_comm]

/-- Concrete finite divisor-layer package for trace, determinant, characteristic determinant,
and the Fibonacci closed trace once the depth counts are identified with Fibonacci numbers. -/
def conclusion_fibadic_depth_radial_operator_trace_determinant_statement : Prop :=
  ∀ (N : ℕ) (support : Finset ℕ) (alpha : ℕ → ℤ) (multiplicity : ℕ → ℕ) (z : ℤ),
    conclusion_fibadic_depth_radial_operator_trace_determinant_trace N support alpha
        multiplicity =
      conclusion_fibadic_depth_radial_operator_trace_determinant_gcdTrace N support alpha
        multiplicity ∧
    conclusion_fibadic_depth_radial_operator_trace_determinant_det N support alpha
        multiplicity =
      (Nat.divisors N).prod (fun d =>
        conclusion_fibadic_depth_radial_operator_trace_determinant_hat support alpha d ^
          multiplicity d) ∧
    conclusion_fibadic_depth_radial_operator_trace_determinant_char N support alpha
        multiplicity z =
      (Nat.divisors N).prod (fun d =>
        (1 - z *
            conclusion_fibadic_depth_radial_operator_trace_determinant_hat support alpha d) ^
          multiplicity d) ∧
    ((∀ m ∈ support,
        (Nat.fib (Nat.gcd m N) : ℤ) =
          ((Nat.divisors N).filter (fun d => d ∣ m)).sum
            (fun d => (multiplicity d : ℤ))) →
      conclusion_fibadic_depth_radial_operator_trace_determinant_trace N support alpha
          multiplicity =
        support.sum (fun m => alpha m * (Nat.fib (Nat.gcd m N) : ℤ)))

/-- Paper label:
`thm:conclusion-fibadic-depth-radial-operator-trace-determinant`. -/
theorem paper_conclusion_fibadic_depth_radial_operator_trace_determinant :
    conclusion_fibadic_depth_radial_operator_trace_determinant_statement := by
  intro N support alpha multiplicity z
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact conclusion_fibadic_depth_radial_operator_trace_determinant_trace_eq_gcdTrace
      N support alpha multiplicity
  · rfl
  · rfl
  · intro hfib
    rw [conclusion_fibadic_depth_radial_operator_trace_determinant_trace_eq_gcdTrace]
    unfold conclusion_fibadic_depth_radial_operator_trace_determinant_gcdTrace
    refine Finset.sum_congr rfl ?_
    intro m hm
    rw [← hfib m hm]

end

end Omega.Conclusion
