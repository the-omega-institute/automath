import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- A complex root `mu` is a critical-circle mode at eigenvalue `lam` iff
    `|mu| = sqrt lam`.
    cor:critical-circle-state-dimension-lower-bound -/
def IsCriticalRoot (lam : ℝ) (mu : ℂ) : Prop :=
  ‖mu‖ = Real.sqrt lam

noncomputable instance (lam : ℝ) (mu : ℂ) : Decidable (IsCriticalRoot lam mu) :=
  Classical.propDecidable _

/-- The sub-multiset of critical-circle roots.
    cor:critical-circle-state-dimension-lower-bound -/
noncomputable def criticalModes (roots : Multiset ℂ) (lam : ℝ) : Multiset ℂ :=
  roots.filter (fun mu => IsCriticalRoot lam mu)

/-- Cardinality of critical modes is bounded by total roots.
    cor:critical-circle-state-dimension-lower-bound -/
theorem criticalModes_card_le (roots : Multiset ℂ) (lam : ℝ) :
    (criticalModes roots lam).card ≤ roots.card := by
  unfold criticalModes
  exact Multiset.card_le_card (Multiset.filter_le _ _)

/-- Paper-facing critical-circle state dimension lower-bound package.
    cor:critical-circle-state-dimension-lower-bound -/
theorem paper_critical_circle_state_dimension_lb :
    (∀ (roots : Multiset ℂ) (lam : ℝ),
      (criticalModes roots lam).card ≤ roots.card) ∧
    (∀ (lam : ℝ), criticalModes (0 : Multiset ℂ) lam = 0) ∧
    (∀ (roots : Multiset ℂ) (lam : ℝ),
      (∀ mu ∈ roots, IsCriticalRoot lam mu) →
      (criticalModes roots lam).card = roots.card) ∧
    (∀ (roots : Multiset ℂ) (lam : ℝ),
      criticalModes roots lam ≤ roots) := by
  refine ⟨criticalModes_card_le, ?_, ?_, ?_⟩
  · intro lam
    unfold criticalModes
    simp
  · intro roots lam hall
    unfold criticalModes
    rw [Multiset.filter_eq_self.mpr]
    intro mu hmu
    exact hall mu hmu
  · intro roots lam
    unfold criticalModes
    exact Multiset.filter_le _ _

end Omega.Zeta
