import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Omega.GU

open Matrix

/-- If an integer square matrix stays nonsingular modulo a prime `p`, then its columns remain
linearly independent after base change to `ℚ`. This is the determinant-level form of lifting a
mod-`p` linear-independence certificate to characteristic `0`.
    lem:modp-independence-lift -/
theorem paper_modp_independence_lift {n : Type*} [Fintype n] [DecidableEq n]
    (p : ℕ) [Fact p.Prime] (A : Matrix n n ℤ)
    (hmodp : (A.map (Int.castRingHom (ZMod p))).det ≠ 0) :
    LinearIndependent ℚ (A.map (Int.castRingHom ℚ)).col := by
  have hdetZ : A.det ≠ 0 := by
    intro hzero
    apply hmodp
    calc
      (A.map (Int.castRingHom (ZMod p))).det = ((A.det : ℤ) : ZMod p) := by
        simpa using (Int.cast_det (R := ZMod p) A).symm
      _ = 0 := by simp [hzero]
  have hdetQ : (A.map (Int.castRingHom ℚ)).det ≠ 0 := by
    intro hzero
    apply hdetZ
    exact Int.cast_eq_zero.mp <| by
      calc
        ((A.det : ℤ) : ℚ) = (A.map (Int.castRingHom ℚ)).det := by
          simpa using (Int.cast_det (R := ℚ) A)
        _ = 0 := hzero
  exact Matrix.linearIndependent_cols_of_det_ne_zero hdetQ

end Omega.GU
