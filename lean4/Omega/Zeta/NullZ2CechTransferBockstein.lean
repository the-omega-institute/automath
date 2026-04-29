import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-null-z2-cech-transfer-bockstein`. -/
theorem paper_xi_null_z2_cech_transfer_bockstein {C1 C2 A : Type*} [BEq C1] [BEq C2]
    (coboundary : C1 -> C2) (pi2 : A -> C2) (beta : C1) (alpha : A) (alpha2 : C2)
    (zero1 : C1) (zero2 : C2) (loopNeg fiberNull : Prop) (hAlpha2 : alpha2 = pi2 alpha)
    (hTransfer : coboundary beta = alpha2) (hNonzero : beta != zero1 <-> alpha2 != zero2)
    (hLoop : loopNeg -> beta != zero1) (hNull : alpha2 != zero2 -> fiberNull) :
    (exists tr : C1 -> C2, tr beta = alpha2) /\ (beta != zero1 <-> alpha2 != zero2) /\
      (loopNeg -> fiberNull) := by
  have _ : alpha2 = pi2 alpha := hAlpha2
  refine ⟨⟨coboundary, hTransfer⟩, hNonzero, ?_⟩
  intro hLoopNeg
  exact hNull (hNonzero.mp (hLoop hLoopNeg))

end Omega.Zeta
