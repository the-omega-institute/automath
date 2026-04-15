import Mathlib.Tactic
import Omega.GU.Window6B3C3TriaxialSelectionIdealFactorization

namespace Omega.GU

open Finset
open scoped BigOperators

set_option maxHeartbeats 400000 in
/-- Explicit quadratic and quartic moment identities on the `window-6` visible `B₃/C₃`
supports.
    thm:window6-b3c3-quartic-defect-onedim -/
theorem paper_window6_b3c3_quartic_defect_onedim (u : ℝ × ℝ × ℝ) :
    let s2 : ℝ := u.1 ^ 2 + u.2.1 ^ 2 + u.2.2 ^ 2
    let s4 : ℝ := u.1 ^ 4 + u.2.1 ^ 4 + u.2.2 ^ 4
    let h4 : ℝ := s4 - (3 / 5 : ℝ) * s2 ^ 2
    (Finset.sum b3VisibleSupport
        (fun w => ((w.1 : ℝ) * u.1 + (w.2.1 : ℝ) * u.2.1 + (w.2.2 : ℝ) * u.2.2) ^ 2) =
        10 * s2) ∧
      (Finset.sum c3VisibleSupport
        (fun w => ((w.1 : ℝ) * u.1 + (w.2.1 : ℝ) * u.2.1 + (w.2.2 : ℝ) * u.2.2) ^ 2) =
        16 * s2) ∧
      (Finset.sum b3VisibleSupport
        (fun w => ((w.1 : ℝ) * u.1 + (w.2.1 : ℝ) * u.2.1 + (w.2.2 : ℝ) * u.2.2) ^ 4) =
        (54 / 5 : ℝ) * s2 ^ 2 - 2 * h4) ∧
      (Finset.sum c3VisibleSupport
        (fun w => ((w.1 : ℝ) * u.1 + (w.2.1 : ℝ) * u.2.1 + (w.2.2 : ℝ) * u.2.2) ^ 4) =
        (144 / 5 : ℝ) * s2 ^ 2 + 28 * h4) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [b3VisibleSupport, zeroWeight, phiB2_12, phiB2_13, phiB2_23]
    ring
  · simp [c3VisibleSupport, zeroWeight, phiC2_12, phiC2_13, phiC2_23]
    ring
  · simp [b3VisibleSupport, zeroWeight, phiB2_12, phiB2_13, phiB2_23]
    ring
  · simp [c3VisibleSupport, zeroWeight, phiC2_12, phiC2_13, phiC2_23]
    ring

end Omega.GU
