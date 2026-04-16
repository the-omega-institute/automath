import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

namespace Omega.GU

/-- The Fibonacci matrix reduced modulo `p`. -/
def fibMatrixMod (p : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod p) :=
  !![(1 : ZMod p), 1; 1, 0]

/-- A matrix is projectively scalar when it becomes a scalar matrix in `PGL₂`. -/
def ProjectivelyScalar {p : ℕ} (A : Matrix (Fin 2) (Fin 2) (ZMod p)) : Prop :=
  ∃ a : ZMod p, A = a • (1 : Matrix (Fin 2) (Fin 2) (ZMod p))

/-- `A` has exact projective order `n` when `A^n` is scalar and no proper positive divisor of `n`
already yields a scalar power. -/
def ProjectiveOrderExact {p : ℕ} (A : Matrix (Fin 2) (Fin 2) (ZMod p)) (n : ℕ) : Prop :=
  ProjectivelyScalar (A ^ n) ∧
    ∀ m : ℕ, 0 < m → m < n → m ∣ n → ¬ ProjectivelyScalar (A ^ m)

/-- Chapter-local package for the Fibonacci-prime projective-order statement. The data keep the
paper hypotheses (`p = F_n` with `n` an odd prime index and `p` prime) together with the two
matrix witnesses used in the proof: the scalarization of `F^n` and the non-scalarity of `F`
itself. -/
structure FibPrimePGL2OrderData where
  n : ℕ
  hnPrime : Nat.Prime n
  hnOdd : Odd n
  hFibPrime : Nat.Prime (Nat.fib n)
  nthPowerScalar : ProjectivelyScalar ((fibMatrixMod (Nat.fib n)) ^ n)
  matrixNotScalar : ¬ ProjectivelyScalar (fibMatrixMod (Nat.fib n))

/-- Paper-facing wrapper for the Fibonacci-prime scalarization phenomenon: once `F^n` is known to
be scalar modulo `p = F_n`, primality of `n` leaves only the trivial proper divisor `1`, and the
nonzero off-diagonal entry rules out projective order `1`. Hence the image of the Fibonacci matrix
has exact order `n` in `PGL₂(𝔽_p)`.
    prop:gut-fibprime-pgl2-order-n -/
theorem paper_gut_fibprime_pgl2_order_n (D : FibPrimePGL2OrderData) :
    ProjectivelyScalar ((fibMatrixMod (Nat.fib D.n)) ^ D.n) ∧
      ProjectiveOrderExact (fibMatrixMod (Nat.fib D.n)) D.n := by
  refine ⟨D.nthPowerScalar, D.nthPowerScalar, ?_⟩
  intro m hmpos hmn hmdvd
  rcases (Nat.dvd_prime D.hnPrime).mp hmdvd with hm1 | hmn'
  · subst hm1
    simpa using D.matrixNotScalar
  · exact False.elim (Nat.lt_irrefl _ (hmn.trans_eq hmn'.symm))

end Omega.GU
