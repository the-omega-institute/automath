import Omega.Conclusion.FibadicDepthRadialOperatorTraceDeterminant

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `cor:conclusion-fibadic-single-depth-projection-rank-gcd`. -/
theorem paper_conclusion_fibadic_single_depth_projection_rank_gcd
    (m N : ℕ) (multiplicity : ℕ → ℕ)
    (hfib : (Nat.fib (Nat.gcd m N) : ℤ) =
      ((Nat.divisors N).filter (fun d => d ∣ m)).sum (fun d => (multiplicity d : ℤ))) :
    conclusion_fibadic_depth_radial_operator_trace_determinant_trace N ({m} : Finset ℕ)
      (fun k => if k = m then 1 else 0) multiplicity =
      (Nat.fib (Nat.gcd m N) : ℤ) := by
  classical
  have hradial :=
    (paper_conclusion_fibadic_depth_radial_operator_trace_determinant
      N ({m} : Finset ℕ) (fun k => if k = m then 1 else 0) multiplicity 0).2.2.2
  have htrace :
      conclusion_fibadic_depth_radial_operator_trace_determinant_trace N ({m} : Finset ℕ)
          (fun k => if k = m then 1 else 0) multiplicity =
        ({m} : Finset ℕ).sum
          (fun k => (if k = m then 1 else 0) * (Nat.fib (Nat.gcd k N) : ℤ)) := by
    refine hradial ?_
    intro k hk
    simpa [Finset.mem_singleton.mp hk] using hfib
  simpa using htrace

end Omega.Conclusion
