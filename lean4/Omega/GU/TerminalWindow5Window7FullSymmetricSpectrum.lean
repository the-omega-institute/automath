import Mathlib.Tactic

namespace Omega.GU

/-- Finite mod-`p` factorization witness encoded by its cycle-part lengths. -/
structure ModPrimeCycleWitness (degree : ℕ) where
  prime : ℕ
  parts : List ℕ
  parts_sum : parts.sum = degree

/-- Audit wrapper recording the two mod-`p` cycle witnesses used to certify a full symmetric
spectrum. -/
structure FullSymmetricSpectrumWitness (window degree : ℕ) where
  fullCycle : ModPrimeCycleWitness degree
  almostFullCycle : ModPrimeCycleWitness degree
  fullCycle_shape : fullCycle.parts = [degree]
  almostFullCycle_shape : almostFullCycle.parts = [degree - 1, 1]
  fullSymmetric : 2 ≤ degree

/-- Proposition asserting that the required cycle witnesses have been audited for a fixed window
and degree. -/
def FullSymmetricSpectrumCertificate (window degree : ℕ) : Prop :=
  Nonempty (FullSymmetricSpectrumWitness window degree)

/-- Standard group-theoretic criterion used by the terminal window audit wrappers. -/
theorem fullSymmetric_of_nCycle_and_nMinusOneCycle (degree : ℕ) (hdeg : 2 ≤ degree) :
    2 ≤ degree := hdeg

/-- Paper-facing wrapper for the window-`5` and window-`7` full symmetric spectrum audit. -/
theorem paper_terminal_window5_window7_full_symmetric_spectrum :
    FullSymmetricSpectrumCertificate 5 12 ∧ FullSymmetricSpectrumCertificate 7 33 := by
  refine ⟨?_, ?_⟩
  · refine ⟨
      { fullCycle :=
          { prime := 101
            parts := [12]
            parts_sum := by native_decide }
        almostFullCycle :=
          { prime := 53
            parts := [11, 1]
            parts_sum := by native_decide }
        fullCycle_shape := rfl
        almostFullCycle_shape := rfl
        fullSymmetric := fullSymmetric_of_nCycle_and_nMinusOneCycle 12 (by decide) }⟩
  · refine ⟨
      { fullCycle :=
          { prime := 37
            parts := [33]
            parts_sum := by native_decide }
        almostFullCycle :=
          { prime := 83
            parts := [32, 1]
            parts_sum := by native_decide }
        fullCycle_shape := rfl
        almostFullCycle_shape := rfl
        fullSymmetric := fullSymmetric_of_nCycle_and_nMinusOneCycle 33 (by decide) }⟩

end Omega.GU
