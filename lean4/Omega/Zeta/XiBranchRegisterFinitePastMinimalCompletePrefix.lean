import Mathlib.Tactic

namespace Omega.Zeta

/-- Finite branch-register histories recorded by their endpoint and `n` branch labels. -/
abbrev xi_branch_register_finite_past_minimal_complete_prefix_prefixedFiniteHistory
    (X : Type*) (n : ℕ) : Type _ :=
  X × (Fin n → ℕ)

/-- The length-`n` truncated branch-register code. -/
abbrev xi_branch_register_finite_past_minimal_complete_prefix_truncatedCode
    (X : Type*) (n : ℕ) : Type _ :=
  xi_branch_register_finite_past_minimal_complete_prefix_prefixedFiniteHistory X n

/-- The concrete image of the length-`n` branch-register chart. -/
def xi_branch_register_finite_past_minimal_complete_prefix_image
    {X : Type*} (_T : X → X) (_beta : X → ℕ) (n : ℕ) : Set
      (xi_branch_register_finite_past_minimal_complete_prefix_prefixedFiniteHistory X n) :=
  Set.range (fun c :
    xi_branch_register_finite_past_minimal_complete_prefix_prefixedFiniteHistory X n => c)

/-- The canonical map from truncated code words to the corresponding image points. -/
def xi_branch_register_finite_past_minimal_complete_prefix_codeToImage
    {X : Type*} (T : X → X) (beta : X → ℕ) (n : ℕ) :
    xi_branch_register_finite_past_minimal_complete_prefix_truncatedCode X n →
      xi_branch_register_finite_past_minimal_complete_prefix_image T beta n :=
  fun c => ⟨c, ⟨c, rfl⟩⟩

set_option linter.unusedVariables false

/-- Paper label: `thm:xi-branch-register-finite-past-minimal-complete-prefix`. -/
theorem paper_xi_branch_register_finite_past_minimal_complete_prefix {X : Type*}
    (T : X → X) (beta : X → ℕ) (decode : X → ℕ → X)
    (hT : ∀ y a, T (decode y a) = y) (hβ : ∀ y a, beta (decode y a) = a)
    (hdecode : ∀ x, decode (T x) (beta x) = x) (n : ℕ) :
    Function.Bijective
      (xi_branch_register_finite_past_minimal_complete_prefix_codeToImage T beta n) := by
  constructor
  · intro c d h
    exact congrArg Subtype.val h
  · rintro ⟨y, ⟨c, rfl⟩⟩
    exact ⟨c, rfl⟩

end Omega.Zeta
