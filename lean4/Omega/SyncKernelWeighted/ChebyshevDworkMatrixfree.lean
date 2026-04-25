import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.SyncKernelWeighted.ChebyshevDworkCongruenceChain

namespace Omega.SyncKernelWeighted

open Polynomial

/-- Paper label: `cor:chebyshev-dwork-matrixfree`. Reducing the already verified integral
Chebyshev--Dwork recurrence coefficientwise modulo `2^k` gives the same closed identity in the
quotient polynomial ring `(ZMod (2^k))[t]`, which is the matrix-free logarithmic-depth wrapper
used in the paper. -/
theorem paper_chebyshev_dwork_matrixfree (D : ChebyshevDworkCongruenceChainData) (k : ℕ) :
    Polynomial.map (Int.castRingHom (ZMod (2 ^ k))) D.P₂ =
      (Polynomial.map (Int.castRingHom (ZMod (2 ^ k))) D.t) ^ 2 *
          Polynomial.map (Int.castRingHom (ZMod (2 ^ k))) D.P₁ -
        Polynomial.map (Int.castRingHom (ZMod (2 ^ k))) D.P₀ := by
  simpa using
    congrArg (Polynomial.map (Int.castRingHom (ZMod (2 ^ k))))
      (paper_chebyshev_dwork_congruence_chain D)

end Omega.SyncKernelWeighted
