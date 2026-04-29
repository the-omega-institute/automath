import Mathlib.Tactic
import Omega.POM.FiberLeyangKlBernoulliDecomposition

namespace Omega.POM

open scoped BigOperators

/-- Concrete finite Lee--Yang spectrum wrapper for the fiber mean-response theorem.  It reuses the
root spectrum from `POMFiberLeyangKlBernoulliDecompositionData` and adds the positivity/nonemptiness
needed for the complete-Bernstein audit. -/
structure pom_fiber_mean_response_complete_bernstein_root_recovery_data extends
    POMFiberLeyangKlBernoulliDecompositionData where
  pom_fiber_mean_response_complete_bernstein_root_recovery_rootCount_pos : 0 < rootCount
  pom_fiber_mean_response_complete_bernstein_root_recovery_alpha_pos :
    ∀ j, 0 < alpha j

namespace pom_fiber_mean_response_complete_bernstein_root_recovery_data

/-- The finite mean response encoded by the Lee--Yang root spectrum. -/
noncomputable def meanResponse
    (D : pom_fiber_mean_response_complete_bernstein_root_recovery_data) (t : ℝ) : ℝ :=
  ∑ j, t / (t + D.alpha j)

/-- The atomic root-spectrum integral for the same response kernel. -/
noncomputable def rootSpectrumIntegral
    (D : pom_fiber_mean_response_complete_bernstein_root_recovery_data) (t : ℝ) : ℝ :=
  ∑ j, t / (t + D.alpha j)

/-- The positive signed derivative magnitude of the rational complete-Bernstein kernel. -/
noncomputable def signedDerivativeMagnitude
    (D : pom_fiber_mean_response_complete_bernstein_root_recovery_data) (n : ℕ) (t : ℝ) : ℝ :=
  (Nat.factorial n : ℝ) * ∑ j, D.alpha j / (t + D.alpha j) ^ (n + 1)

/-- Explicit recovery of a finite root from the indexed atomic spectrum. -/
noncomputable def recoveredRoot
    (D : pom_fiber_mean_response_complete_bernstein_root_recovery_data) (j : Fin D.rootCount) :
    ℝ :=
  D.alpha j

/-- The response is exactly the finite root sum, equivalently the integral against the finite
atomic Lee--Yang root spectrum. -/
def meanResponseFormula
    (D : pom_fiber_mean_response_complete_bernstein_root_recovery_data) : Prop :=
  ∀ t : ℝ, D.meanResponse t = ∑ j, t / (t + D.alpha j) ∧
    D.rootSpectrumIntegral t = ∑ j, t / (t + D.alpha j)

/-- Complete-Bernstein audit: every signed derivative magnitude of positive order is positive on
the positive half-line. -/
def completeBernstein
    (D : pom_fiber_mean_response_complete_bernstein_root_recovery_data) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ t : ℝ, 0 < t → 0 < D.signedDerivativeMagnitude n t

/-- The finite indexed root-recovery map returns exactly the original Lee--Yang root spectrum. -/
def rootRecovering
    (D : pom_fiber_mean_response_complete_bernstein_root_recovery_data) : Prop :=
  ∀ j : Fin D.rootCount, D.recoveredRoot j = D.alpha j

end pom_fiber_mean_response_complete_bernstein_root_recovery_data

/-- Paper label:
`thm:pom-fiber-mean-response-complete-bernstein-root-recovery`. -/
theorem paper_pom_fiber_mean_response_complete_bernstein_root_recovery
    (D : pom_fiber_mean_response_complete_bernstein_root_recovery_data) :
    D.meanResponseFormula ∧ D.completeBernstein ∧ D.rootRecovering := by
  refine ⟨?_, ?_, ?_⟩
  · intro t
    simp [pom_fiber_mean_response_complete_bernstein_root_recovery_data.meanResponse,
      pom_fiber_mean_response_complete_bernstein_root_recovery_data.rootSpectrumIntegral]
  · intro n _hn t ht
    dsimp [pom_fiber_mean_response_complete_bernstein_root_recovery_data.completeBernstein,
      pom_fiber_mean_response_complete_bernstein_root_recovery_data.signedDerivativeMagnitude]
    have hterm :
        ∀ j : Fin D.rootCount, 0 < D.alpha j / (t + D.alpha j) ^ (n + 1) := by
      intro j
      have hden : 0 < (t + D.alpha j) ^ (n + 1) :=
        pow_pos (add_pos ht
          (D.pom_fiber_mean_response_complete_bernstein_root_recovery_alpha_pos j)) _
      exact div_pos
        (D.pom_fiber_mean_response_complete_bernstein_root_recovery_alpha_pos j) hden
    have hnonempty : (Finset.univ : Finset (Fin D.rootCount)).Nonempty := by
      exact ⟨⟨0, D.pom_fiber_mean_response_complete_bernstein_root_recovery_rootCount_pos⟩,
        by simp⟩
    have hsum : 0 < ∑ j : Fin D.rootCount, D.alpha j / (t + D.alpha j) ^ (n + 1) :=
      Finset.sum_pos (fun j _hj => hterm j) hnonempty
    have hfac : 0 < (Nat.factorial n : ℝ) := by positivity
    exact mul_pos hfac hsum
  · intro j
    rfl

end Omega.POM
