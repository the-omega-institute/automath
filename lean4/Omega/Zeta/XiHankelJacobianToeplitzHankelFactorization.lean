import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Matrix

/-- Lower-triangular Toeplitz matrix associated to a coefficient stream. -/
def xi_hankel_jacobian_toeplitz_hankel_factorization_toeplitz
    {k : Type*} [Zero k] (d : ℕ) (s : ℕ → k) : Matrix (Fin d) (Fin d) k :=
  fun n i => if (i : ℕ) ≤ n then s (n - i) else 0

/-- Truncated reciprocal-series datum: multiplication by `q` followed by multiplication by `s`
is the identity on coefficients of degree `< d`. -/
def xi_hankel_jacobian_toeplitz_hankel_factorization_truncatedInverse
    {k : Type*} [Semiring k] (d : ℕ) (q s : ℕ → k) : Prop :=
  (xi_hankel_jacobian_toeplitz_hankel_factorization_toeplitz d s *
      xi_hankel_jacobian_toeplitz_hankel_factorization_toeplitz d q) =
    (1 : Matrix (Fin d) (Fin d) k)

/-- The Hankel-recurrence Jacobian identity before replacing the recurrence Toeplitz block by
its truncated inverse. -/
def xi_hankel_jacobian_toeplitz_hankel_factorization_recurrenceJacobianIdentity
    {k : Type*} [Ring k] (d : ℕ) (q : ℕ → k)
    (jacobian hankel : Matrix (Fin d) (Fin d) k) : Prop :=
  (xi_hankel_jacobian_toeplitz_hankel_factorization_toeplitz d q * jacobian) = -hankel

/-- Paper-facing statement for
`prop:xi-hankel-jacobian-toeplitz-hankel-factorization`.

The reciprocal-series coefficients `s` give the truncated inverse Toeplitz block for `q`; after
left-multiplying the known Hankel-recurrence Jacobian identity by that inverse, the Jacobian
factors as `-T(c)H(c)`. -/
def xi_hankel_jacobian_toeplitz_hankel_factorization_statement : Prop :=
  ∀ {k : Type*} [Field k] (d : ℕ) (q s : ℕ → k)
      (jacobian hankel : Matrix (Fin d) (Fin d) k),
    xi_hankel_jacobian_toeplitz_hankel_factorization_truncatedInverse d q s →
    xi_hankel_jacobian_toeplitz_hankel_factorization_recurrenceJacobianIdentity
      d q jacobian hankel →
      jacobian =
        -(xi_hankel_jacobian_toeplitz_hankel_factorization_toeplitz d s * hankel)

/-- Paper label: `prop:xi-hankel-jacobian-toeplitz-hankel-factorization`. -/
theorem paper_xi_hankel_jacobian_toeplitz_hankel_factorization :
    xi_hankel_jacobian_toeplitz_hankel_factorization_statement := by
  intro k hk d q s jacobian hankel hinv hjac
  let L := xi_hankel_jacobian_toeplitz_hankel_factorization_toeplitz d q
  let T := xi_hankel_jacobian_toeplitz_hankel_factorization_toeplitz d s
  have hleft : T * L = (1 : Matrix (Fin d) (Fin d) k) := by
    simpa [T, L] using hinv
  have hrec : L * jacobian = -hankel := by
    simpa [L] using hjac
  calc
    jacobian = (1 : Matrix (Fin d) (Fin d) k) * jacobian := by simp
    _ = (T * L) * jacobian := by rw [hleft]
    _ = T * (L * jacobian) := by rw [mul_assoc]
    _ = T * (-hankel) := by rw [hrec]
    _ = -(T * hankel) := by simp
    _ = -(xi_hankel_jacobian_toeplitz_hankel_factorization_toeplitz d s * hankel) := by
      rfl

end Omega.Zeta
