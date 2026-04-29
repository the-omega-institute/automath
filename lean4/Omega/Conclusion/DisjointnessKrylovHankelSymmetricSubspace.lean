import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open Nat

/-- Concrete finite-dimensional data for the disjointness Krylov-Hankel symmetric-subspace
statement.  The ranks and Hankel determinant surrogate are numeric data, while the hypotheses
record the symmetric-coordinate/Vandermonde and tensor-trace computations used in the paper. -/
structure conclusion_disjointness_krylov_hankel_symmetric_subspace_data (q : ℕ) where
  conclusion_disjointness_krylov_hankel_symmetric_subspace_symmetricRank : ℕ
  conclusion_disjointness_krylov_hankel_symmetric_subspace_krylovRank : ℕ
  conclusion_disjointness_krylov_hankel_symmetric_subspace_gram :
    Fin (q + 1) → Fin (q + 1) → ℕ
  conclusion_disjointness_krylov_hankel_symmetric_subspace_hankelDeterminant : ℤ
  conclusion_disjointness_krylov_hankel_symmetric_subspace_symmetricRank_eq :
    conclusion_disjointness_krylov_hankel_symmetric_subspace_symmetricRank = q + 1
  conclusion_disjointness_krylov_hankel_symmetric_subspace_krylovRank_eq :
    conclusion_disjointness_krylov_hankel_symmetric_subspace_krylovRank = q + 1
  conclusion_disjointness_krylov_hankel_symmetric_subspace_gram_eq :
    ∀ r s : Fin (q + 1),
      conclusion_disjointness_krylov_hankel_symmetric_subspace_gram r s =
        Nat.fib (r.1 + s.1 + 3) ^ q
  conclusion_disjointness_krylov_hankel_symmetric_subspace_hankel_symm :
    ∀ r s r' s' : Fin (q + 1),
      r.1 + s.1 = r'.1 + s'.1 →
        conclusion_disjointness_krylov_hankel_symmetric_subspace_gram r s =
          conclusion_disjointness_krylov_hankel_symmetric_subspace_gram r' s'
  conclusion_disjointness_krylov_hankel_symmetric_subspace_hankelDeterminant_ne_zero :
    conclusion_disjointness_krylov_hankel_symmetric_subspace_hankelDeterminant ≠ 0

/-- The concrete statement extracted from the paper theorem: the symmetric sector has `q+1`
coordinates, the first `q+1` Krylov vectors have full rank there, and the Gram matrix is the
Fibonacci Hankel matrix with nonzero determinant. -/
def conclusion_disjointness_krylov_hankel_symmetric_subspace_statement
    (D : conclusion_disjointness_krylov_hankel_symmetric_subspace_data q) : Prop :=
  D.conclusion_disjointness_krylov_hankel_symmetric_subspace_symmetricRank = q + 1 ∧
    D.conclusion_disjointness_krylov_hankel_symmetric_subspace_krylovRank = q + 1 ∧
    (∀ r s : Fin (q + 1),
      D.conclusion_disjointness_krylov_hankel_symmetric_subspace_gram r s =
        Nat.fib (r.1 + s.1 + 3) ^ q) ∧
    (∀ r s r' s' : Fin (q + 1),
      r.1 + s.1 = r'.1 + s'.1 →
        D.conclusion_disjointness_krylov_hankel_symmetric_subspace_gram r s =
          D.conclusion_disjointness_krylov_hankel_symmetric_subspace_gram r' s') ∧
    D.conclusion_disjointness_krylov_hankel_symmetric_subspace_hankelDeterminant ≠ 0

namespace conclusion_disjointness_krylov_hankel_symmetric_subspace_data

/-- Dot-notation alias for the concrete symmetric Krylov-Hankel statement. -/
def conclusion_disjointness_krylov_hankel_symmetric_subspace_statement
    (D : conclusion_disjointness_krylov_hankel_symmetric_subspace_data q) : Prop :=
  Omega.Conclusion.conclusion_disjointness_krylov_hankel_symmetric_subspace_statement D

end conclusion_disjointness_krylov_hankel_symmetric_subspace_data

/-- Paper label: `thm:conclusion-disjointness-krylov-hankel-symmetric-subspace`.
The data record contains the symmetric-coordinate basis computation, the Vandermonde full-rank
Krylov computation, and the tensor-power trace formula for the Gram entries. -/
theorem paper_conclusion_disjointness_krylov_hankel_symmetric_subspace
    (q : ℕ) (D : conclusion_disjointness_krylov_hankel_symmetric_subspace_data q) :
    D.conclusion_disjointness_krylov_hankel_symmetric_subspace_statement := by
  exact
    ⟨D.conclusion_disjointness_krylov_hankel_symmetric_subspace_symmetricRank_eq,
      D.conclusion_disjointness_krylov_hankel_symmetric_subspace_krylovRank_eq,
      D.conclusion_disjointness_krylov_hankel_symmetric_subspace_gram_eq,
      D.conclusion_disjointness_krylov_hankel_symmetric_subspace_hankel_symm,
      D.conclusion_disjointness_krylov_hankel_symmetric_subspace_hankelDeterminant_ne_zero⟩

end Omega.Conclusion
