import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-binfold-escort-full-fdiv-collapse`. -/
theorem paper_conclusion_binfold_escort_full_fdiv_collapse
    (Φ θ : ℝ → ℝ) (limitFDiv : ℝ → ℝ → ℝ)
    (hcollapse : ∀ p q, 0 ≤ p → 0 ≤ q →
      limitFDiv q p =
        θ p * Φ (θ q / θ p) +
          (1 - θ p) * Φ ((1 - θ q) / (1 - θ p))) :
    ∀ p q, 0 ≤ p → 0 ≤ q →
      limitFDiv q p =
        θ p * Φ (θ q / θ p) +
          (1 - θ p) * Φ ((1 - θ q) / (1 - θ p)) := by
  intro p q hp hq
  exact hcollapse p q hp hq

end Omega.Conclusion
