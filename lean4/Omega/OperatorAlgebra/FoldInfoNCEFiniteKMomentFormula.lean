import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Folding.MomentSum

namespace Omega.OperatorAlgebra

open scoped BigOperators
noncomputable section

/-- Normalized collision moment `c_q(m) = S_q(m) / 2^{qm}`. -/
def foldCollisionMomentNormalized (q m : ℕ) : ℝ :=
  (Omega.momentSum q m : ℝ) / (2 : ℝ) ^ (q * m)

/-- The explicit coefficient
`β_{K,q} = binom(K-1,q-1) * Σ_{j=0}^{q-1} binom(q-1,j) (-1)^{q-1-j} log(1+j)`. -/
def foldInfoNCEBeta (K q : ℕ) : ℝ :=
  (Nat.choose (K - 1) (q - 1) : ℝ) *
    Finset.sum (Finset.range q) fun j =>
      (Nat.choose (q - 1) j : ℝ) * (-1 : ℝ) ^ (q - 1 - j) * Real.log (j + 1)

/-- The finite-`K` moment expansion with the explicit `β_{K,q}` coefficients. -/
def foldInfoNCEFiniteKMomentExpansion (m K : ℕ) : ℝ :=
  Finset.sum (Finset.Icc 2 K) fun q => foldInfoNCEBeta K q * foldCollisionMomentNormalized q m

/-- Paper-facing finite-`K` moment formulas. The explicit coefficient family `β_{K,q}` packages the
moment expansion, and for `K = 2, 3` the expansion collapses to the two-term combinations indexed
by `q = 2, 3`.
    prop:op-algebra-fold-infonce-finiteK-moment-formula -/
theorem paper_op_algebra_fold_infonce_finiteK_moment_formula (m : ℕ) :
    foldInfoNCEFiniteKMomentExpansion m 2 =
      foldInfoNCEBeta 2 2 * foldCollisionMomentNormalized 2 m ∧
      foldInfoNCEFiniteKMomentExpansion m 3 =
        foldInfoNCEBeta 3 2 * foldCollisionMomentNormalized 2 m +
          foldInfoNCEBeta 3 3 * foldCollisionMomentNormalized 3 m := by
  refine ⟨?_, ?_⟩
  · rw [foldInfoNCEFiniteKMomentExpansion]
    norm_num
  · rw [foldInfoNCEFiniteKMomentExpansion]
    rw [show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide]
    simp

end
end Omega.OperatorAlgebra
