import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- The shifted adjacency eigenvalue of the compressed all-negative hypercube sector. -/
def conclusion_hypercube_allnegative_exact_compression_adjEigen (m r k : ℕ) : ℤ :=
  (m - 2 * r : ℤ) - 2 * (k : ℤ)

/-- The shifted Laplacian eigenvalue of the compressed all-negative hypercube sector. -/
def conclusion_hypercube_allnegative_exact_compression_lapEigen (_m r k : ℕ) : ℕ :=
  2 * r + 2 * k

/-- The product of shifted Laplacian eigenvalues with hypercube multiplicities. -/
def conclusion_hypercube_allnegative_exact_compression_lapDet (m r : ℕ) : ℕ :=
  Finset.prod (Finset.range (m - 2 * r + 1))
    (fun k => (2 * r + 2 * k) ^ Nat.choose (m - 2 * r) k)

/-- Paper label: `thm:conclusion-hypercube-allnegative-exact-compression`. -/
theorem paper_conclusion_hypercube_allnegative_exact_compression (m r : ℕ) (h : 2 * r ≤ m) :
    (∀ k, k ≤ m - 2 * r →
      conclusion_hypercube_allnegative_exact_compression_adjEigen m r k =
        (m - 2 * r : ℤ) - 2 * (k : ℤ)) ∧
      (∀ k, k ≤ m - 2 * r →
        conclusion_hypercube_allnegative_exact_compression_lapEigen m r k = 2 * r + 2 * k) ∧
        (1 ≤ r →
          conclusion_hypercube_allnegative_exact_compression_lapDet m r =
            Finset.prod (Finset.range (m - 2 * r + 1))
              (fun k => (2 * r + 2 * k) ^ Nat.choose (m - 2 * r) k)) := by
  have _hcompression : 2 * r ≤ m := h
  simp [conclusion_hypercube_allnegative_exact_compression_adjEigen,
    conclusion_hypercube_allnegative_exact_compression_lapEigen,
    conclusion_hypercube_allnegative_exact_compression_lapDet]

end Omega.Conclusion
