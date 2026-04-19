import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Matrix

/-- The `κ = 2` Prony Jacobian, with columns ordered as `(ω₁, ω₂, a₁, a₂)` and rows indexed by
the moments `s₀, s₁, s₂, s₃`.
    thm:xi-prony-moment-map-jacobian-delta4 -/
def pronyJacobian2 (a₁ a₂ ω₁ ω₂ : ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 1, 0, 0;
     a₁, a₂, ω₁, ω₂;
     a₁ ^ 2, a₂ ^ 2, 2 * ω₁ * a₁, 2 * ω₂ * a₂;
     a₁ ^ 3, a₂ ^ 3, 3 * ω₁ * a₁ ^ 2, 3 * ω₂ * a₂ ^ 2]

private theorem det_fin_four {R : Type*} [CommRing R] (M : Matrix (Fin 4) (Fin 4) R) :
    M.det =
      M 0 0 * M 1 1 * M 2 2 * M 3 3 - M 0 0 * M 1 1 * M 2 3 * M 3 2
      - M 0 0 * M 1 2 * M 2 1 * M 3 3 + M 0 0 * M 1 2 * M 2 3 * M 3 1
      + M 0 0 * M 1 3 * M 2 1 * M 3 2 - M 0 0 * M 1 3 * M 2 2 * M 3 1
      - M 0 1 * M 1 0 * M 2 2 * M 3 3 + M 0 1 * M 1 0 * M 2 3 * M 3 2
      + M 0 1 * M 1 2 * M 2 0 * M 3 3 - M 0 1 * M 1 2 * M 2 3 * M 3 0
      - M 0 1 * M 1 3 * M 2 0 * M 3 2 + M 0 1 * M 1 3 * M 2 2 * M 3 0
      + M 0 2 * M 1 0 * M 2 1 * M 3 3 - M 0 2 * M 1 0 * M 2 3 * M 3 1
      - M 0 2 * M 1 1 * M 2 0 * M 3 3 + M 0 2 * M 1 1 * M 2 3 * M 3 0
      + M 0 2 * M 1 3 * M 2 0 * M 3 1 - M 0 2 * M 1 3 * M 2 1 * M 3 0
      - M 0 3 * M 1 0 * M 2 1 * M 3 2 + M 0 3 * M 1 0 * M 2 2 * M 3 1
      + M 0 3 * M 1 1 * M 2 0 * M 3 2 - M 0 3 * M 1 1 * M 2 2 * M 3 0
      - M 0 3 * M 1 2 * M 2 0 * M 3 1 + M 0 3 * M 1 2 * M 2 1 * M 3 0 := by
  rw [det_succ_row_zero, Fin.sum_univ_four]
  simp only [det_fin_three, submatrix_apply,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    show Fin.succ (2 : Fin 3) = (3 : Fin 4) from rfl,
    show (0 : Fin 4).succAbove (0 : Fin 3) = 1 from by decide,
    show (0 : Fin 4).succAbove (1 : Fin 3) = 2 from by decide,
    show (0 : Fin 4).succAbove (2 : Fin 3) = 3 from by decide,
    show (1 : Fin 4).succAbove (0 : Fin 3) = 0 from by decide,
    show (1 : Fin 4).succAbove (1 : Fin 3) = 2 from by decide,
    show (1 : Fin 4).succAbove (2 : Fin 3) = 3 from by decide,
    show (2 : Fin 4).succAbove (0 : Fin 3) = 0 from by decide,
    show (2 : Fin 4).succAbove (1 : Fin 3) = 1 from by decide,
    show (2 : Fin 4).succAbove (2 : Fin 3) = 3 from by decide,
    show (3 : Fin 4).succAbove (0 : Fin 3) = 0 from by decide,
    show (3 : Fin 4).succAbove (1 : Fin 3) = 1 from by decide,
    show (3 : Fin 4).succAbove (2 : Fin 3) = 2 from by decide,
    show (0 : Fin 4).val = 0 from rfl, show (1 : Fin 4).val = 1 from rfl,
    show (2 : Fin 4).val = 2 from rfl, show (3 : Fin 4).val = 3 from rfl]
  ring

set_option maxHeartbeats 400000 in
/-- Explicit `κ = 2` Jacobian determinant: one value column and one derivative column per node
produce the fourth power of the Vandermonde factor.
    thm:xi-prony-moment-map-jacobian-delta4 -/
theorem paper_xi_prony_moment_map_jacobian_delta4 (a₁ a₂ ω₁ ω₂ : ℤ) :
    (pronyJacobian2 a₁ a₂ ω₁ ω₂).det = -ω₁ * ω₂ * (a₂ - a₁) ^ 4 := by
  rw [det_fin_four]
  simp [pronyJacobian2]
  ring

end Omega.Zeta
