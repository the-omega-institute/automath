import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Omega.Folding

/-- Paper-facing wrapper for entropy preservation under the finite-to-one factor from `Z_m` to
`Y_m`.
    cor:Phi_m-entropy-no-drop -/
theorem paper_Phi_m_entropy_no_drop (m : Nat) (hTopZ hTopY : ℝ)
    (conjToFullShift finiteToOneFactor : Prop)
    (hConj : conjToFullShift -> hTopZ = Real.log 2)
    (hFactor : finiteToOneFactor -> hTopY = hTopZ) :
    2 <= m -> conjToFullShift -> finiteToOneFactor -> hTopY = Real.log 2 := by
  intro _ hmConj hmFactor
  calc
    hTopY = hTopZ := hFactor hmFactor
    _ = Real.log 2 := hConj hmConj

end Omega.Folding
