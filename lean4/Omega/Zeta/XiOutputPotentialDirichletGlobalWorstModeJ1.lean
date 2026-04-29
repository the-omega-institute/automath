import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-output-potential-dirichlet-global-worst-mode-j1`. -/
theorem paper_xi_output_potential_dirichlet_global_worst_mode_j1
    (r : ℝ → ℝ) (angle rho : ℕ → ℕ → ℝ) (eta delta : ℝ) (heta : 0 < eta)
    (hdelta : 0 < delta)
    (hlocal : ∀ x y : ℝ, 0 ≤ x → x < y → y ≤ eta → r y < r x)
    (hfar : ∀ t : ℝ, eta ≤ t → t ≤ Real.pi → r t ≤ 1 - delta)
    (heventual :
      ∃ m0 : ℕ,
        ∀ m ≥ m0,
          0 ≤ angle m 1 ∧
            angle m 1 < eta ∧
              1 - delta < r (angle m 1) ∧
                ∀ j : ℕ,
                  2 ≤ j →
                    j ≤ m - 2 →
                      angle m 1 < angle m j ∧
                        (angle m j ≤ eta ∨ eta ≤ angle m j ∧ angle m j ≤ Real.pi))
    (hrho : ∀ m j : ℕ, rho m j = r (angle m j))
    (hconj : ∀ m : ℕ, rho m (m - 1) = rho m 1) :
    ∃ m0 : ℕ,
      ∀ m ≥ m0,
        rho m 1 = rho m (m - 1) ∧
          ∀ j : ℕ, 2 ≤ j → j ≤ m - 2 → rho m j < rho m 1 := by
  have _heta := heta
  have _hdelta := hdelta
  rcases heventual with ⟨m0, hm0⟩
  refine ⟨m0, ?_⟩
  intro m hm
  rcases hm0 m hm with ⟨hangle1_nonneg, hangle1_lt_eta, hrho1_gt, hmode⟩
  constructor
  · exact (hconj m).symm
  · intro j hj2 hjle
    rcases hmode j hj2 hjle with ⟨hangle_lt, hsmall | hlarge⟩
    · rw [hrho m j, hrho m 1]
      exact hlocal (angle m 1) (angle m j) hangle1_nonneg hangle_lt hsmall
    · rw [hrho m j, hrho m 1]
      exact lt_of_le_of_lt (hfar (angle m j) hlarge.1 hlarge.2) hrho1_gt

end Omega.Zeta
