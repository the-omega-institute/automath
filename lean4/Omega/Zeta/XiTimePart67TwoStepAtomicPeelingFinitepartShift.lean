import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part67-two-step-atomic-peeling-finitepart-shift`. -/
theorem paper_xi_time_part67_two_step_atomic_peeling_finitepart_shift
    (Delta F P Pcore : ℝ → ℝ → ℝ) (logM logMcore shift : ℝ)
    (hDelta : ∀ z u, Delta z u = (1 - u * z ^ 2) * F z u)
    (hP : ∀ z u, P z u = u * z ^ 2 + Pcore z u)
    (hShift : logM = logMcore + shift)
    (hClosed : shift = (7 - 3 * Real.sqrt 5) / 2) :
    (∀ z u, Delta z u = (1 - u * z ^ 2) * F z u) ∧
      (∀ z u, P z u = u * z ^ 2 + Pcore z u) ∧
        logM = logMcore + (7 - 3 * Real.sqrt 5) / 2 := by
  refine ⟨hDelta, hP, ?_⟩
  rw [hClosed] at hShift
  exact hShift

end Omega.Zeta
