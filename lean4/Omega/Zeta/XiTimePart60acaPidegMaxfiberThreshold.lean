import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part60aca-pideg-maxfiber-threshold`. If the standard-identity
threshold is exactly the max fiber size `D`, then the PI degree is `D`, the identity holds at
`2 * PIdeg`, and the preceding even degree fails whenever `PIdeg` is positive. -/
theorem paper_xi_time_part60aca_pideg_maxfiber_threshold
    (D PIdeg : ℕ) (modelsStd : ℕ → Prop) (hPI : PIdeg = D)
    (hmodels : ∀ r, modelsStd (2 * r) ↔ D ≤ r) :
    PIdeg = D ∧ modelsStd (2 * PIdeg) ∧
      (0 < PIdeg → ¬ modelsStd (2 * PIdeg - 2)) := by
  refine ⟨hPI, ?_, ?_⟩
  · rw [hmodels PIdeg]
    omega
  · intro hpos hprev
    have hrewrite : 2 * PIdeg - 2 = 2 * (PIdeg - 1) := by omega
    rw [hrewrite] at hprev
    have hle : D ≤ PIdeg - 1 := (hmodels (PIdeg - 1)).1 hprev
    omega

end Omega.Zeta
