import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part60acb-constant-fiber-free-group-action-criterion`.
The supplied realizability criterion is exactly the constant-fiber condition; the window-6
fibers of sizes `2` and `3` rule out any such constant, hence rule out both free-orbit and
abelian-coset realizability. -/
theorem paper_xi_time_part60acb_constant_fiber_free_group_action_criterion {X : Type*}
    [Fintype X] (fiberCard : X → ℕ) (freeOrbitRealizable abelianCosetRealizable : Prop)
    (hFreeConst : freeOrbitRealizable → ∃ D : ℕ, 0 < D ∧ ∀ x, fiberCard x = D)
    (hConstFree : (∃ D : ℕ, 0 < D ∧ ∀ x, fiberCard x = D) → freeOrbitRealizable)
    (hAbelian : abelianCosetRealizable → ∃ D : ℕ, 0 < D ∧ ∀ x, fiberCard x = D)
    (hWindow6 : (∃ x y : X, fiberCard x = 2 ∧ fiberCard y = 3) ∧
      ∃ z : X, fiberCard z = 4) :
    (freeOrbitRealizable ↔ ∃ D : ℕ, 0 < D ∧ ∀ x, fiberCard x = D) ∧
      ¬ freeOrbitRealizable ∧ ¬ abelianCosetRealizable := by
  rcases hWindow6.1 with ⟨x, y, hx, hy⟩
  refine ⟨⟨hFreeConst, hConstFree⟩, ?_, ?_⟩
  · intro hFree
    rcases hFreeConst hFree with ⟨D, _hDpos, hconst⟩
    have hD2 : D = 2 := (hconst x).symm.trans hx
    have hD3 : D = 3 := (hconst y).symm.trans hy
    omega
  · intro hAbelianRealizable
    rcases hAbelian hAbelianRealizable with ⟨D, _hDpos, hconst⟩
    have hD2 : D = 2 := (hconst x).symm.trans hx
    have hD3 : D = 3 := (hconst y).symm.trans hy
    omega

end Omega.Zeta
