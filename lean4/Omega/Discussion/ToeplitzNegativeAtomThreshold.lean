import Mathlib

namespace Omega.Discussion

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the Toeplitz threshold separating PSD persistence from an
exposed negative atom.
    prop:discussion-toeplitz-negative-atom-threshold -/
theorem paper_discussion_toeplitz_negative_atom_threshold
    (m0 M0 ε : ℝ) (N : ℕ) (toeplitzPSD defectExposed : Prop)
    (hPSD : ε ≤ m0 / (N + 1 : ℝ) → toeplitzPSD)
    (hExpose : M0 / (N + 1 : ℝ) < ε → defectExposed) :
    (ε ≤ m0 / (N + 1 : ℝ) → toeplitzPSD) ∧
      (M0 / (N + 1 : ℝ) < ε → defectExposed) := by
  exact ⟨hPSD, hExpose⟩

end Omega.Discussion
