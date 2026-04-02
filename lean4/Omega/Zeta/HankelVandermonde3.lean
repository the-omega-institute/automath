import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Matrix

def hankel3 (ω1 ω2 ω3 a1 a2 a3 : ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  let s0 := ω1 + ω2 + ω3
  let s1 := ω1 * a1^2^0 + ω2 * a2^2^0 + ω3 * a3^2^0
  let s2 := ω1 * a1^2 + ω2 * a2^2 + ω3 * a3^2
  let s3 := ω1 * a1^3 + ω2 * a2^3 + ω3 * a3^3
  let s4 := ω1 * a1^4 + ω2 * a2^4 + ω3 * a3^4
  !![ω1 + ω2 + ω3, ω1 * a1 + ω2 * a2 + ω3 * a3, s2;
     ω1 * a1 + ω2 * a2 + ω3 * a3, s2, s3;
     s2, s3, s4]

/-- 3×3 Hankel determinant equals the weighted Vandermonde square.
    cor:xi-hankel-vs-prony-square-gap -/
theorem hankel3_vandermonde_square
    (ω1 ω2 ω3 a1 a2 a3 : ℤ) :
    (hankel3 ω1 ω2 ω3 a1 a2 a3).det =
      ω1 * ω2 * ω3 * (a2 - a1)^2 * (a3 - a1)^2 * (a3 - a2)^2 := by
  rw [Matrix.det_fin_three]
  unfold hankel3
  ring

end Omega.Zeta
