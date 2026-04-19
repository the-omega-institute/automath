import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Defs
import Omega.OperatorAlgebra.FoldGaugeGroupStructure

namespace Omega.OperatorAlgebra

open scoped BigOperators

/-- The truncated fixed-point MGF term coming from the classical falling-factorial moments of a
uniform permutation. -/
def fixedPointMomentTerm (y : ℚ) (k : ℕ) : ℚ :=
  y ^ k / Nat.factorial k

/-- Fiberwise fixed-point MGF for a fiber of cardinality `n`. -/
def fiberFixedPointMgf (n : ℕ) (y : ℚ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), fixedPointMomentTerm y k

/-- The fold-orbit fixed-point MGF obtained by summing the fiberwise truncation indices over the
product of fiber ranges. -/
def foldOrbitMgf {m : ℕ} (N : Fin m → ℕ) (y : ℚ) : ℚ :=
  ∑ s ∈ Fintype.piFinset (fun d => Finset.range (N d + 1)), ∏ d, fixedPointMomentTerm y (s d)

/-- Burnside's diagonal action factors the fold gauge group into fiberwise symmetric groups, and the
resulting fixed-point MGF splits as the product of the fiber MGFs. The proof is the finite-product
identity `prod_univ_sum`.  `thm:op-algebra-fold-orbit-mgf-fiber-factorization` -/
theorem paper_op_algebra_fold_orbit_mgf_fiber_factorization {m : ℕ}
    (N : Fin m → ℕ) (y : ℚ) :
    foldGaugeGroupOrder N = ∏ d, Nat.factorial (N d) ∧
      foldOrbitMgf N y = ∏ d, fiberFixedPointMgf (N d) y := by
  constructor
  · rfl
  · symm
    simpa [foldOrbitMgf, fiberFixedPointMgf, fixedPointMomentTerm] using
      (Finset.prod_univ_sum
        (t := fun d => Finset.range (N d + 1))
        (f := fun d k => fixedPointMomentTerm y k))

end Omega.OperatorAlgebra
