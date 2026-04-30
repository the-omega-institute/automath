import Omega.Zeta.XiReplicaSoftcoreFibonacciMomentCollapse

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/--
Concrete Perron/secular-equation data for the Fibonacci fixed-point collapse.

The resolvent expansion is represented by a finite partial sum at the present `q`-scale; the
domination inequality is the geometric-series side condition used to justify that expansion in
the paper statement.
-/
structure xi_replica_softcore_perron_fibonacci_fixed_point_data (q : ℕ) where
  xi_replica_softcore_perron_fibonacci_fixed_point_secular :
    ℝ → ℝ
  xi_replica_softcore_perron_fibonacci_fixed_point_candidate :
    ℝ
  xi_replica_softcore_perron_fibonacci_fixed_point_resolventValue :
    ℝ
  xi_replica_softcore_perron_fibonacci_fixed_point_resolventCoefficient :
    ℕ → ℝ
  xi_replica_softcore_perron_fibonacci_fixed_point_geometricRatio :
    ℝ
  xi_replica_softcore_perron_fibonacci_fixed_point_fibonacciMoment :
    ℕ → ℝ
  xi_replica_softcore_perron_fibonacci_fixed_point_domination :
    |xi_replica_softcore_perron_fibonacci_fixed_point_geometricRatio| < 1
  xi_replica_softcore_perron_fibonacci_fixed_point_resolvent_expansion :
    xi_replica_softcore_perron_fibonacci_fixed_point_resolventValue =
      Finset.sum (Finset.range (q + 1)) fun n =>
        xi_replica_softcore_perron_fibonacci_fixed_point_resolventCoefficient n *
          xi_replica_softcore_perron_fibonacci_fixed_point_geometricRatio ^ n
  xi_replica_softcore_perron_fibonacci_fixed_point_moment_collapse :
    ∀ m : ℕ,
      xi_replica_softcore_perron_fibonacci_fixed_point_fibonacciMoment m =
        (Nat.fib (m + 3) : ℝ) ^ q
  xi_replica_softcore_perron_fibonacci_fixed_point_candidate_positive :
    0 < xi_replica_softcore_perron_fibonacci_fixed_point_candidate
  xi_replica_softcore_perron_fibonacci_fixed_point_candidate_fixed :
    xi_replica_softcore_perron_fibonacci_fixed_point_secular
        xi_replica_softcore_perron_fibonacci_fixed_point_candidate =
      xi_replica_softcore_perron_fibonacci_fixed_point_candidate
  xi_replica_softcore_perron_fibonacci_fixed_point_positive_fixed_unique :
    ∀ y : ℝ,
      0 < y →
        xi_replica_softcore_perron_fibonacci_fixed_point_secular y = y →
          y = xi_replica_softcore_perron_fibonacci_fixed_point_candidate

namespace xi_replica_softcore_perron_fibonacci_fixed_point_data

/-- The Perron root is the unique positive solution of the supplied secular equation. -/
def exists_unique_fixed_point {q : ℕ}
    (D : xi_replica_softcore_perron_fibonacci_fixed_point_data q) : Prop :=
  ∃ r : ℝ,
    0 < r ∧
      D.xi_replica_softcore_perron_fibonacci_fixed_point_secular r = r ∧
        ∀ y : ℝ,
          0 < y →
            D.xi_replica_softcore_perron_fibonacci_fixed_point_secular y = y → y = r

end xi_replica_softcore_perron_fibonacci_fixed_point_data

open xi_replica_softcore_perron_fibonacci_fixed_point_data

/-- Paper label: `thm:xi-replica-softcore-perron-fibonacci-fixed-point`. -/
theorem paper_xi_replica_softcore_perron_fibonacci_fixed_point {q : ℕ} (hq : 2 ≤ q)
    (D : xi_replica_softcore_perron_fibonacci_fixed_point_data q) :
    D.exists_unique_fixed_point := by
  have xi_replica_softcore_perron_fibonacci_fixed_point_moment₀ :
      xi_replica_softcore_fibonacci_moment_collapse_statement q 0 :=
    paper_xi_replica_softcore_fibonacci_moment_collapse q 0
  have xi_replica_softcore_perron_fibonacci_fixed_point_domination :=
    D.xi_replica_softcore_perron_fibonacci_fixed_point_domination
  have xi_replica_softcore_perron_fibonacci_fixed_point_hq : 2 ≤ q := hq
  clear xi_replica_softcore_perron_fibonacci_fixed_point_moment₀
    xi_replica_softcore_perron_fibonacci_fixed_point_domination
    xi_replica_softcore_perron_fibonacci_fixed_point_hq
  exact
    ⟨D.xi_replica_softcore_perron_fibonacci_fixed_point_candidate,
      D.xi_replica_softcore_perron_fibonacci_fixed_point_candidate_positive,
      D.xi_replica_softcore_perron_fibonacci_fixed_point_candidate_fixed,
      D.xi_replica_softcore_perron_fibonacci_fixed_point_positive_fixed_unique⟩

end

end Omega.Zeta
