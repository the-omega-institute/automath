import Omega.Folding.Defect

namespace Omega

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for prefix-map functoriality in the fold-truncation paper.
    The stable-word restriction covers both `\pi_{n \to m}` and `r_{n \to m}` on admissible words,
    while `restrictWord` handles the ambient cube map `\tau_{n \to m}` and xor compatibility.
    lem:pi-functorial-golden -/
theorem paper_fold_truncation_pi_functorial_golden
    (h₁ : m ≤ n) (h₂ : n ≤ k) (x : X k) (u v : Word k) :
    X.restrictLE h₁ (X.restrictLE h₂ x) = X.restrictLE (Nat.le_trans h₁ h₂) x ∧
      restrictWord h₁ (restrictWord h₂ u) = restrictWord (Nat.le_trans h₁ h₂) u ∧
      restrictWord (Nat.le_trans h₁ h₂) (xorWord u v) =
        xorWord (restrictWord (Nat.le_trans h₁ h₂) u)
          (restrictWord (Nat.le_trans h₁ h₂) v) := by
  exact ⟨X.restrict_functorial h₁ h₂ x, restrictWord_comp h₁ h₂ u,
    restrictWord_xor (Nat.le_trans h₁ h₂) u v⟩

end Omega
