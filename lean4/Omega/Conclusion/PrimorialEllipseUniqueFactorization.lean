import Mathlib.Tactic
import Omega.Conclusion.AffineNormalFormSemidirect
import Omega.Conclusion.PrimorialMixedRadixAffine

namespace Omega.Conclusion

open Omega.Conclusion.AffineNormalFormSemidirect
open Omega.Conclusion.PrimorialMixedRadixAffine

/-- The `2,3,5` primorial ellipse code, written in mixed-radix coordinates and read back as an
index in `Fin 30`. -/
def primorialEllipseCode3 (k : Fin 30) : Fin 30 :=
  ⟨mixedRadixEncode3 (mixedRadixDecode3_1 k) (mixedRadixDecode3_2 k) (mixedRadixDecode3_3 k),
    mixedRadixEncode3_lt _ _ _
      (by
        simp [mixedRadixDecode3_1]
        exact Nat.mod_lt _ (by decide))
      (by
        simp [mixedRadixDecode3_2]
        exact Nat.mod_lt _ (by decide))
      (by
        simp [mixedRadixDecode3_3]
        exact Nat.mod_lt _ (by decide))⟩

/-- The primorial ellipse code collapses the ordered gate product to the affine normal form
`A_{30,k}`. -/
theorem primorialEllipseCode3_affine_normal_form (k : Fin 30) :
    A_N_k 2 (mixedRadixDecode3_1 k) * A_N_k 3 (mixedRadixDecode3_2 k) *
        A_N_k 5 (mixedRadixDecode3_3 k) =
      A_N_k 30 (primorialEllipseCode3 k) := by
  simpa [primorialEllipseCode3] using
    (affineCollapse3 (mixedRadixDecode3_1 k) (mixedRadixDecode3_2 k) (mixedRadixDecode3_3 k))

/-- Decoding and then re-encoding a point of the primorial ellipse leaves it unchanged. -/
theorem primorialEllipseCode3_eq_self (k : Fin 30) :
    primorialEllipseCode3 k = k := by
  apply Fin.ext
  simp [primorialEllipseCode3, mixedRadixEncode3_right_inverse, k.2]

/-- Paper package: the `2,3,5` primorial ellipse code is bijective.
    thm:conclusion-primorial-ellipse-unique-factorization -/
theorem paper_conclusion_primorial_ellipse_unique_factorization :
    Function.Bijective primorialEllipseCode3 := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    calc
      x = primorialEllipseCode3 x := (primorialEllipseCode3_eq_self x).symm
      _ = primorialEllipseCode3 y := hxy
      _ = y := primorialEllipseCode3_eq_self y
  · intro y
    exact ⟨y, primorialEllipseCode3_eq_self y⟩

end Omega.Conclusion
