import Omega.POM.RenyiHalfHellingerTensorAdditivity

namespace Omega.POM

theorem paper_pom_small_distortion_constant_tensor_multiplicative {α β : Type*} [Fintype α]
    [Fintype β] (w : α → ℝ) (v : β → ℝ) (hw : ∀ a, 0 ≤ w a) (hv : ∀ b, 0 ≤ v b)
    (hwpos : 0 < pomHellingerHalfSum w) (hvpos : 0 < pomHellingerHalfSum v) :
    ((pomHellingerHalfSum (pomTensorWeight w v)) ^ 2 - 1) =
      (pomHellingerHalfSum w ^ 2 - 1) + (pomHellingerHalfSum v ^ 2 - 1) +
        (pomHellingerHalfSum w ^ 2 - 1) * (pomHellingerHalfSum v ^ 2 - 1) := by
  have _ : 0 < pomHellingerHalfSum w * pomHellingerHalfSum v := mul_pos hwpos hvpos
  rw [pomHellingerHalfSum_tensor w v hw hv]
  ring

end Omega.POM
