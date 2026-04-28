import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-fibadic-koopman-depth-algebra-joint-spectrum`. -/
theorem paper_conclusion_fibadic_koopman_depth_algebra_joint_spectrum
    (blockDiagonalization scaledBlockCharacteristic globalCharacteristic spectralDescription : Prop)
    (hBlock : blockDiagonalization)
    (hScaled : blockDiagonalization → scaledBlockCharacteristic)
    (hGlobal : scaledBlockCharacteristic → globalCharacteristic)
    (hSpectral : globalCharacteristic → spectralDescription) :
    blockDiagonalization ∧ scaledBlockCharacteristic ∧ globalCharacteristic ∧
      spectralDescription := by
  exact ⟨hBlock, hScaled hBlock, hGlobal (hScaled hBlock),
    hSpectral (hGlobal (hScaled hBlock))⟩

end Omega.Conclusion
