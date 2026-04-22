import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

namespace Omega.Zeta

open Matrix

/-- The Adams-pushed coefficient sequence obtained by sampling the original moments at multiples
of `m`. -/
def xi_adams_pushforward_toeplitz_principal_minor_monotonicity_coeff
    (m : ℕ) (c : ℤ → ℝ) (n : ℤ) : ℝ :=
  c ((m : ℤ) * n)

/-- The concrete Toeplitz truncation attached to an integer-indexed moment sequence. -/
def xi_adams_pushforward_toeplitz_principal_minor_monotonicity_toeplitz
    (N : ℕ) (c : ℤ → ℝ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun i j => c ((j : ℤ) - (i : ℤ))

/-- The index embedding selecting the multiples of `m` inside `{0, ..., mN}`. -/
def xi_adams_pushforward_toeplitz_principal_minor_monotonicity_embedding
    (m N : ℕ) : Fin (N + 1) → Fin (m * N + 1) :=
  fun i =>
    ⟨m * i.1, by
      have hi : i.1 ≤ N := Nat.le_of_lt_succ i.is_lt
      have hmul : m * i.1 ≤ m * N := Nat.mul_le_mul_left m hi
      omega⟩

lemma xi_adams_pushforward_toeplitz_principal_minor_monotonicity_toeplitz_eq_submatrix
    (m N : ℕ) (c : ℤ → ℝ) :
    xi_adams_pushforward_toeplitz_principal_minor_monotonicity_toeplitz N
        (xi_adams_pushforward_toeplitz_principal_minor_monotonicity_coeff m c) =
      (xi_adams_pushforward_toeplitz_principal_minor_monotonicity_toeplitz (m * N) c).submatrix
        (xi_adams_pushforward_toeplitz_principal_minor_monotonicity_embedding m N)
        (xi_adams_pushforward_toeplitz_principal_minor_monotonicity_embedding m N) := by
  ext i j
  simp [xi_adams_pushforward_toeplitz_principal_minor_monotonicity_toeplitz,
    xi_adams_pushforward_toeplitz_principal_minor_monotonicity_coeff,
    xi_adams_pushforward_toeplitz_principal_minor_monotonicity_embedding]
  congr 1
  ring

/-- Under the Adams pushforward `ξ ↦ ξ^m`, the sampled coefficient sequence is exactly
`c_{mn}`; the corresponding Toeplitz truncation is the principal submatrix of the original
Toeplitz block indexed by multiples of `m`, hence Toeplitz positive semidefiniteness descends
to the pushed-forward truncation.
    prop:xi-adams-pushforward-toeplitz-principal-minor-monotonicity -/
theorem paper_xi_adams_pushforward_toeplitz_principal_minor_monotonicity
    (m N : ℕ) (c : ℤ → ℝ)
    (hpsd :
      (xi_adams_pushforward_toeplitz_principal_minor_monotonicity_toeplitz (m * N) c).PosSemidef) :
    (∀ n : ℤ,
        xi_adams_pushforward_toeplitz_principal_minor_monotonicity_coeff m c n =
          c ((m : ℤ) * n)) ∧
      xi_adams_pushforward_toeplitz_principal_minor_monotonicity_toeplitz N
          (xi_adams_pushforward_toeplitz_principal_minor_monotonicity_coeff m c) =
        (xi_adams_pushforward_toeplitz_principal_minor_monotonicity_toeplitz (m * N) c).submatrix
          (xi_adams_pushforward_toeplitz_principal_minor_monotonicity_embedding m N)
          (xi_adams_pushforward_toeplitz_principal_minor_monotonicity_embedding m N) ∧
      (xi_adams_pushforward_toeplitz_principal_minor_monotonicity_toeplitz N
          (xi_adams_pushforward_toeplitz_principal_minor_monotonicity_coeff m c)).PosSemidef := by
  refine ⟨fun n => rfl, ?_, ?_⟩
  · exact
      xi_adams_pushforward_toeplitz_principal_minor_monotonicity_toeplitz_eq_submatrix m N c
  · rw [xi_adams_pushforward_toeplitz_principal_minor_monotonicity_toeplitz_eq_submatrix]
    exact hpsd.submatrix _

end Omega.Zeta
