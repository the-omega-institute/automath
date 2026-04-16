import Omega.Folding.PhiSlidingBlockCode

namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Wrapper theorem matching the JNT publication label.
    prop:Phi-m-equivariant -/
theorem paper_resolution_phi_m_equivariant_seeds
    {A B : Type*} (m : ℕ) (f : (Fin m → A) → B) (s : ℤ → A) :
    slideBlockCode m f (shiftSeq s) = shiftSeq (slideBlockCode m f s) :=
  slideBlockCode_shift_equivariant m f s

/-- Packaged form of the shift-equivariance wrapper.
    prop:Phi-m-equivariant -/
theorem paper_resolution_phi_m_equivariant_package
    {A B : Type*} (m : ℕ) (f : (Fin m → A) → B) (s : ℤ → A) :
    slideBlockCode m f (shiftSeq s) = shiftSeq (slideBlockCode m f s) :=
  paper_resolution_phi_m_equivariant_seeds m f s

end Omega.Folding
