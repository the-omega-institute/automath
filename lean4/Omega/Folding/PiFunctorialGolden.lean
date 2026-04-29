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

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the coordinatewise functoriality of finite truncations and its
specialization to infinite legal sequences.
    lem:pi-functorial-golden -/
theorem paper_pi_functorial_golden
    (h₁ : m₁ ≤ m₂) (h₂ : m₂ ≤ m₃) (x : X m₃) (c : X.XInfinity) :
    X.restrictLE h₁ (X.restrictLE h₂ x) = X.restrictLE (Nat.le_trans h₁ h₂) x ∧
      X.restrictLE h₁ (X.prefixWord c m₂) = X.prefixWord c m₁ := by
  refine ⟨X.restrict_functorial h₁ h₂ x, ?_⟩
  apply Subtype.ext
  funext i
  rfl

end Omega
