import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-visible-anom-iff-radial-wallcrossing`. -/
theorem paper_xi_visible_anom_iff_radial_wallcrossing {Channel : Type*} (anomalyZero : Prop)
    (N : Channel -> Nat -> Nat) (hzero : anomalyZero ↔ ∀ chi n, N chi n = 0)
    (hwall : ¬ anomalyZero ↔ ∃ chi n, N chi n < N chi (n + 1)) :
    (anomalyZero ↔ ∀ chi n, N chi n = 0) ∧
      (¬ anomalyZero ↔ ∃ chi n, N chi n < N chi (n + 1)) := by
  exact ⟨hzero, hwall⟩

end Omega.Zeta
