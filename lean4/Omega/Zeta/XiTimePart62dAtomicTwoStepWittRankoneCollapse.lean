import Mathlib.Tactic

namespace Omega.Zeta

lemma xi_time_part62d_atomic_two_step_witt_rankone_collapse_off_two
    (u : ℚ) (p pCore : ℕ → ℚ)
    (hpeel : ∀ n, p n = pCore n + if n = 2 then u else 0) :
    ∀ n, n ≠ 2 → p n = pCore n := by
  intro n hn
  have h := hpeel n
  simpa [hn] using h

lemma xi_time_part62d_atomic_two_step_witt_rankone_collapse_at_two
    (u : ℚ) (p pCore : ℕ → ℚ)
    (hpeel : ∀ n, p n = pCore n + if n = 2 then u else 0) :
    p 2 = u + pCore 2 := by
  have h := hpeel 2
  simpa [add_comm] using h

/-- Paper label: `thm:xi-time-part62d-atomic-two-step-witt-rankone-collapse`. -/
theorem paper_xi_time_part62d_atomic_two_step_witt_rankone_collapse
    (u : ℚ) (p pCore : ℕ → ℚ)
    (hpeel : ∀ n, p n = pCore n + if n = 2 then u else 0) :
    (∀ n, n ≠ 2 → p n = pCore n) ∧ p 2 = u + pCore 2 := by
  exact ⟨
    xi_time_part62d_atomic_two_step_witt_rankone_collapse_off_two u p pCore hpeel,
    xi_time_part62d_atomic_two_step_witt_rankone_collapse_at_two u p pCore hpeel⟩

end Omega.Zeta
