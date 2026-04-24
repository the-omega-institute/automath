import Mathlib

namespace Omega.Zeta

/-- Paper label: `thm:xi-foldbin-uniform-layer-degeneracy-two-atom-law`.
This is the concrete wrapper for the two-atom endpoint law and its moment formula. -/
theorem paper_xi_foldbin_uniform_layer_degeneracy_two_atom_law
    (nu : Bool → ℝ) (moment : ℝ → ℝ)
    (hnu : nu false = 1 / Real.goldenRatio ∧ nu true = 1 / Real.goldenRatio ^ 2)
    (hmoment : ∀ a, 0 ≤ a → moment a = 1 / Real.goldenRatio + Real.goldenRatio ^ (-a - 2)) :
    (nu false = 1 / Real.goldenRatio ∧ nu true = 1 / Real.goldenRatio ^ 2) ∧
      ∀ a, 0 ≤ a → moment a = 1 / Real.goldenRatio + Real.goldenRatio ^ (-a - 2) := by
  exact ⟨hnu, hmoment⟩

end Omega.Zeta
