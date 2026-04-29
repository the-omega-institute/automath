import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-cmv-finite-window-spectral-functor-finite-representability`. -/
theorem paper_conclusion_cmv_finite_window_spectral_functor_finite_representability {α : Type*}
    (entry : ℕ → ℕ → ℕ → ℕ → α) (limitEntry : ℕ → ℕ → ℕ → α)
    (hFreeze :
      ∀ N r,
        ∃ Lstar,
          ∀ L i j,
            Lstar ≤ L → i ≤ N → j ≤ N → entry L r i j = limitEntry r i j) :
    ∀ N m,
      ∃ Lstar,
        ∀ L i j r,
          Lstar ≤ L → i ≤ N → j ≤ N → r ≤ m → entry L r i j = limitEntry r i j := by
  intro N m
  induction m with
  | zero =>
      obtain ⟨Lstar, hLstar⟩ := hFreeze N 0
      refine ⟨Lstar, ?_⟩
      intro L i j r hL hi hj hr
      have hr0 : r = 0 := by omega
      subst r
      exact hLstar L i j hL hi hj
  | succ m ih =>
      obtain ⟨Lprev, hprev⟩ := ih
      obtain ⟨Lone, hone⟩ := hFreeze N (m + 1)
      refine ⟨max Lprev Lone, ?_⟩
      intro L i j r hL hi hj hr
      by_cases hrm : r ≤ m
      · exact hprev L i j r (le_trans (Nat.le_max_left Lprev Lone) hL) hi hj hrm
      · have hr_succ : r = m + 1 := by omega
        subst r
        exact hone L i j (le_trans (Nat.le_max_right Lprev Lone) hL) hi hj

end Omega.Conclusion
