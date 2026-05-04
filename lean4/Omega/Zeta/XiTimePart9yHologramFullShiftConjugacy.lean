import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9y-hologram-full-shift-conjugacy`. -/
theorem paper_xi_time_part9y_hologram_full_shift_conjugacy {E X : Type*} [DecidableEq E]
    (F : E → X → X) (π : (ℕ → E) → X) (shift : (ℕ → E) → (ℕ → E)) (R : X → X)
    (hπ : Function.Bijective π) (hdecomp : ∀ e, π e = F (e 0) (π (shift e)))
    (hR : ∀ a x, R (F a x) = x) :
    Function.Bijective π ∧ (∀ e, R (π e) = π (shift e)) := by
  refine ⟨hπ, ?_⟩
  intro e
  rw [hdecomp e]
  exact hR (e 0) (π (shift e))

end Omega.Zeta
