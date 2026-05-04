import Mathlib

namespace Omega.Conclusion

/-- Concrete hypotheses for the hot-phase no-ghost-sector package: the thermal coordinate stays in
the open unit interval, the Legendre slope is `1 - qstar`, the oracle pressure is strictly concave
on the hot interval, and each hot point is the unique exposed contact point. -/
def conclusion_hot_phase_no_ghost_sector_hypotheses
    (Gamma qstar : ℝ → ℝ) (a0 a1 : ℝ) : Prop :=
  (∀ a : ℝ, a ∈ Set.Ioo a0 a1 → qstar a ∈ Set.Ioo (0 : ℝ) 1) ∧
    (∀ a : ℝ, a ∈ Set.Ioo a0 a1 → deriv Gamma a = 1 - qstar a) ∧
    StrictConcaveOn ℝ (Set.Ioo a0 a1) Gamma ∧
    (∀ a : ℝ, a ∈ Set.Ioo a0 a1 →
      ∃! α : ℝ, α ∈ Set.Ioo a0 a1 ∧ α = a)

/-- Concrete conclusion for the hot-phase no-ghost-sector theorem. It exposes the open interval
bounds on `qstar`, the reciprocal derivative bounds on `Gamma'`, strict concavity, and uniqueness
of the exposed point in the hot phase. -/
def conclusion_hot_phase_no_ghost_sector_conclusion
    (Gamma qstar : ℝ → ℝ) (a0 a1 : ℝ) : Prop :=
  (∀ a : ℝ, a ∈ Set.Ioo a0 a1 →
      qstar a ∈ Set.Ioo (0 : ℝ) 1 ∧ deriv Gamma a ∈ Set.Ioo (0 : ℝ) 1) ∧
    StrictConcaveOn ℝ (Set.Ioo a0 a1) Gamma ∧
    (∀ a : ℝ, a ∈ Set.Ioo a0 a1 →
      ∃! α : ℝ, α ∈ Set.Ioo a0 a1 ∧ α = a)

/-- Paper label: `thm:conclusion-hot-phase-no-ghost-sector`. -/
theorem paper_conclusion_hot_phase_no_ghost_sector (Gamma qstar : ℝ → ℝ) (a0 a1 : ℝ)
    (h : conclusion_hot_phase_no_ghost_sector_hypotheses Gamma qstar a0 a1) :
    conclusion_hot_phase_no_ghost_sector_conclusion Gamma qstar a0 a1 := by
  rcases h with ⟨hqstar, hderiv, hconcave, hexposed⟩
  refine ⟨?_, hconcave, hexposed⟩
  intro a ha
  have hq := hqstar a ha
  have hd := hderiv a ha
  refine ⟨hq, ?_⟩
  rw [hd]
  exact ⟨by linarith [hq.2], by linarith [hq.1]⟩

end Omega.Conclusion
