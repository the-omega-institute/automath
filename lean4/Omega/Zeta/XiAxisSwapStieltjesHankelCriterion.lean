import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-axis-swap-stieltjes-hankel-criterion`. -/
theorem paper_xi_axis_swap_stieltjes_hankel_criterion
    (RH : Prop) (stieltjes completeMonotone hankelPSD : ℝ → Prop)
    (hRS : RH ↔ ∀ x, stieltjes x)
    (hSC : (∀ x, stieltjes x) ↔ ∀ x, completeMonotone x)
    (hCH : (∀ x, completeMonotone x) ↔ ∀ x, hankelPSD x) :
    RH ↔ ((∀ x, stieltjes x) ∧ (∀ x, completeMonotone x) ∧ (∀ x, hankelPSD x)) := by
  constructor
  · intro hRH
    have hS : ∀ x, stieltjes x := hRS.mp hRH
    have hC : ∀ x, completeMonotone x := hSC.mp hS
    have hH : ∀ x, hankelPSD x := hCH.mp hC
    exact ⟨hS, hC, hH⟩
  · intro h
    exact hRS.mpr h.1

end Omega.Zeta
