import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The collision sum before merging two nonempty blocks. -/
def coarseGrainingCollisionBefore (background dA dB : ℝ) : ℝ :=
  background + dA ^ 2 + dB ^ 2

/-- The collision sum after merging the blocks into a single block. -/
def coarseGrainingCollisionAfter (background dA dB : ℝ) : ℝ :=
  background + (dA + dB) ^ 2

/-- The global visible Walsh energy obtained from the collision-deficit identity. -/
def coarseGrainingVisibleWalshEnergy (total collision : ℝ) : ℝ :=
  total - collision

/-- Paper-facing arithmetic core of the conclusion-layer coarse-graining argument: a genuine merge
strictly increases the collision sum, and the collision-deficit identity turns that into strict
visible-energy dissipation.
    cor:conclusion-coarse-graining-consumes-visible-walsh-energy -/
theorem paper_conclusion_coarse_graining_consumes_visible_walsh_energy
    (totalVisible background dA dB : ℝ) (hA : 0 < dA) (hB : 0 < dB) :
    coarseGrainingCollisionBefore background dA dB <
      coarseGrainingCollisionAfter background dA dB ∧
    coarseGrainingVisibleWalshEnergy totalVisible
        (coarseGrainingCollisionAfter background dA dB) <
      coarseGrainingVisibleWalshEnergy totalVisible
        (coarseGrainingCollisionBefore background dA dB) := by
  have hcollision :
      coarseGrainingCollisionBefore background dA dB <
        coarseGrainingCollisionAfter background dA dB := by
    unfold coarseGrainingCollisionBefore coarseGrainingCollisionAfter
    nlinarith [mul_pos hA hB]
  refine ⟨hcollision, ?_⟩
  unfold coarseGrainingVisibleWalshEnergy
  linarith

end Omega.Conclusion
