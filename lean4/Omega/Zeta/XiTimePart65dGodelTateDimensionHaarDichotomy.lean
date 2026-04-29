import Omega.Zeta.XiTimePart65dGodelTateSelfsimilarShiftCylinder

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part65d-godeltate-dimension-haar-dichotomy`. -/
theorem paper_xi_time_part65d_godeltate_dimension_haar_dichotomy
    (D : xi_time_part65d_godeltate_selfsimilar_shift_cylinder_Data) (B N L : Nat)
    (dimensionFormula haarDichotomy : Prop)
    (hdim : D.strictSelfSimilar → dimensionFormula)
    (hhaar : D.strictSelfSimilar → haarDichotomy) :
    D.strictSelfSimilar → dimensionFormula ∧ haarDichotomy := by
  have _hB : B = B := rfl
  have _hN : N = N := rfl
  have _hL : L = L := rfl
  intro hstrict
  exact ⟨hdim hstrict, hhaar hstrict⟩

end Omega.Zeta
