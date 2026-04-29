import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-finite-window-true-resonance-index`.
The finite-window resonance index is packaged from a monotonicity hypothesis and the
Toeplitz-PSD/RH equivalence: a failure of RH forces a finite nonzero index. -/
theorem paper_xi_finite_window_true_resonance_index
    (RH : Prop) (kappa : ℕ → ℕ)
    (hmono : ∀ {M N : ℕ}, M ≤ N → kappa M ≤ kappa N)
    (hRH : (∀ N, kappa N = 0) ↔ RH) :
    (∀ {M N : ℕ}, M ≤ N → kappa M ≤ kappa N) ∧
      (¬ RH → ∃ N, 1 ≤ kappa N) ∧
        ((∀ N, kappa N = 0) ↔ RH) := by
  refine ⟨hmono, ?_, hRH⟩
  intro hNotRH
  by_contra hNoWitness
  apply hNotRH
  exact hRH.mp fun N => by
    have hNoPositive : ¬ 1 ≤ kappa N := fun hPositive => hNoWitness ⟨N, hPositive⟩
    omega

end Omega.Zeta
