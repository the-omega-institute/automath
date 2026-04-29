import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-local-index-equals-local-time-fiber`. -/
theorem paper_xi_local_index_equals_local_time_fiber
    (X : Type) (index minTimeDim fiberCard alphabetSize tMin : X → ℕ)
    (hMin : ∀ x, minTimeDim x = index x) (hFiber : ∀ x, fiberCard x = index x)
    (hTime : ∀ x, alphabetSize x ^ tMin x ≥ index x) :
    (∀ x, minTimeDim x = index x) ∧
      (∀ x, index x = fiberCard x) ∧
        (∀ x, alphabetSize x ^ tMin x ≥ index x) := by
  exact ⟨hMin, fun x => (hFiber x).symm, hTime⟩

end Omega.Zeta
