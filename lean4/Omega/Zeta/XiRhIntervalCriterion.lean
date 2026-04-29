import Mathlib.Data.Complex.Basic

namespace Omega.Zeta

/-- Paper label: `prop:xi-rh-interval-criterion`. Zeros transported through the completed
coordinate `S = y + y⁻¹` satisfy the critical-line criterion exactly when all roots of the
compressed polynomial satisfy the corresponding closed-interval predicate. -/
theorem paper_xi_rh_interval_criterion (Xi P : ℂ → ℂ)
    (criticalLine closedInterval : ℂ → Prop) (yOf sOf : ℂ → ℂ)
    (hzero : ∀ s : ℂ, Xi s = 0 → P (yOf s + (yOf s)⁻¹) = 0)
    (hcover : ∀ s : ℂ, Xi s = 0 → sOf (yOf s) = s)
    (hroot : ∀ S : ℂ, P S = 0 → ∃ y : ℂ, S = y + y⁻¹ ∧ Xi (sOf y) = 0)
    (hcrit : ∀ y : ℂ, criticalLine (sOf y) ↔ closedInterval (y + y⁻¹)) :
    (∀ s : ℂ, Xi s = 0 → criticalLine s) ↔
      (∀ S : ℂ, P S = 0 → closedInterval S) := by
  constructor
  · intro hXi S hP
    rcases hroot S hP with ⟨y, hS, hy⟩
    have hclosed : closedInterval (y + y⁻¹) := (hcrit y).1 (hXi (sOf y) hy)
    rwa [hS]
  · intro hP s hs
    have hclosed : closedInterval (yOf s + (yOf s)⁻¹) := hP _ (hzero s hs)
    have hcrit_sOf : criticalLine (sOf (yOf s)) := (hcrit (yOf s)).2 hclosed
    simpa [hcover s hs] using hcrit_sOf

end Omega.Zeta
