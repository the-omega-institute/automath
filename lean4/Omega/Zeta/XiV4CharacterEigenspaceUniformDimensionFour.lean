import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-v4-character-eigenspace-uniform-dimension-four`. -/
theorem paper_xi_v4_character_eigenspace_uniform_dimension_four {χ : Type*} [DecidableEq χ]
    (trivial : χ) (dim : χ → ℕ) (htriv : dim trivial = 4)
    (hnontriv : ∀ c, c ≠ trivial → dim c = 7 - 4 + 1) : ∀ c, dim c = 4 := by
  intro c
  by_cases hc : c = trivial
  · subst c
    exact htriv
  · have hdim := hnontriv c hc
    norm_num at hdim
    exact hdim

end Omega.Zeta
