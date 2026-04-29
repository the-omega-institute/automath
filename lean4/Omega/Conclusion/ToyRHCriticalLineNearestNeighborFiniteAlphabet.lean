import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-toyrh-critical-line-nearest-neighbor-finite-alphabet`.

A nearest-neighbor gap sequence whose values all lie in a fixed finite phase-gap alphabet has
finite range. -/
theorem paper_conclusion_toyrh_critical_line_nearest_neighbor_finite_alphabet
    (nearestGap : ℕ → ℝ) (G : Finset ℝ) (hmem : ∀ n, nearestGap n ∈ G) :
    (Set.range nearestGap).Finite := by
  have hsubset : Set.range nearestGap ⊆ (G : Set ℝ) := by
    rintro x ⟨n, rfl⟩
    exact hmem n
  exact G.finite_toSet.subset hsubset

end Omega.Conclusion
