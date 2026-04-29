import Mathlib.Data.Int.Basic
import Mathlib.Tactic
import Omega.Zeta.FiniteDefectCompleteReconstruction

namespace Omega.Conclusion

open Omega.Zeta

/-- The number of visible modes in the shallow/large-window dichotomy. -/
def conclusion_finite_toeplitz_falsifier_nyquist_depth_barrier_visible_modes
    (κ hminInv N : ℕ) : ℕ :=
  if N < hminInv then κ - 1 else κ

/-- The relabelled candidate offline fibers; in the stabilized regime they are independent of the
window length. -/
def conclusion_finite_toeplitz_falsifier_nyquist_depth_barrier_offline_fiber
    {κ : ℕ} (π : Equiv.Perm (Fin κ)) (fiber : Fin κ → ℤ) (_N : ℕ) : Fin κ → ℤ :=
  fun j => fiber (π j)

lemma conclusion_finite_toeplitz_falsifier_nyquist_depth_barrier_eventual_stability
    (κ : ℕ) (nuMinus : ℕ → ℕ) (hStable : ∃ N0, ∀ N ≥ N0, nuMinus N = κ) :
    ∃ N0, (∀ N ≥ N0, nuMinus N = κ) ∧ ∀ N ≥ N0, nuMinus N ≤ κ := by
  rcases hStable with ⟨N0, hN0⟩
  refine ⟨N0, hN0, ?_⟩
  intro N hN
  rw [hN0 N hN]

/-- Paper label: `thm:conclusion-finite-toeplitz-falsifier-nyquist-depth-barrier`.
Below the `h_min^{-1}` scale the visible-mode count is capped by `κ - 1`; once the negative
inertia sequence stabilizes to `κ`, the finite-defect package supplies the readable/reconstructible
`κ`-mode regime, and the relabelled candidate offline fibers are already stable. -/
theorem paper_conclusion_finite_toeplitz_falsifier_nyquist_depth_barrier
    (κ hminInv : ℕ) (D : FiniteDefectCompleteReconstructionData κ) (nuMinus : ℕ → ℕ)
    (fiber : Fin κ → ℤ) (π : Equiv.Perm (Fin κ))
    (hStable : ∃ N0, ∀ N ≥ N0, nuMinus N = κ) :
    (∀ N,
      N < hminInv →
        conclusion_finite_toeplitz_falsifier_nyquist_depth_barrier_visible_modes κ hminInv N ≤
          κ - 1) ∧
      (∃ N0, (∀ N ≥ N0, nuMinus N = κ) ∧ ∀ N ≥ N0, nuMinus N ≤ κ) ∧
      D.kappaReadable ∧
      D.reconstructionFrom4KappaSamples ∧
      D.reconstructionFromMomentSegment ∧
      ∀ N ≥ hminInv,
        conclusion_finite_toeplitz_falsifier_nyquist_depth_barrier_visible_modes κ hminInv N = κ ∧
          conclusion_finite_toeplitz_falsifier_nyquist_depth_barrier_offline_fiber π fiber N =
            conclusion_finite_toeplitz_falsifier_nyquist_depth_barrier_offline_fiber
              π fiber hminInv := by
  rcases conclusion_finite_toeplitz_falsifier_nyquist_depth_barrier_eventual_stability
      κ nuMinus hStable with ⟨N0, hN0, hLe⟩
  rcases paper_xi_finite_defect_complete_reconstruction κ D with ⟨hkappa, h4kappa, h2kappa, _⟩
  refine ⟨?_, ⟨N0, hN0, hLe⟩, hkappa, h4kappa, h2kappa, ?_⟩
  · intro N hN
    simp [conclusion_finite_toeplitz_falsifier_nyquist_depth_barrier_visible_modes, hN]
  · intro N hN
    refine ⟨?_, ?_⟩
    · simp [conclusion_finite_toeplitz_falsifier_nyquist_depth_barrier_visible_modes,
        Nat.not_lt.mpr hN]
    · ext j
      rfl

end Omega.Conclusion
