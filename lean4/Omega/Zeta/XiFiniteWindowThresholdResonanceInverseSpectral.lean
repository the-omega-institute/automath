import Mathlib.Tactic
import Omega.Zeta.XiToeplitzDetVerblunsky

namespace Omega.Zeta

/-- Paper label: `thm:xi-finite-window-threshold-resonance-inverse-spectral`.
Any boundary Schur/Verblunsky modulus violation contributes a nonempty failure set.  The supplied
Toeplitz determinant/Verblunsky theorem controls the least failure index, yielding a finite
nonpositive Toeplitz determinant witness. -/
theorem paper_xi_finite_window_threshold_resonance_inverse_spectral
    (D : Omega.Zeta.XiToeplitzDetVerblunskyData)
    (hBoundary : ∃ j < D.steps, 1 ≤ |D.alphaAt j|) :
    D.detProductFactorization ∧ D.minimalFailureIndexControl ∧
      ∃ m, m ∈ D.failureSet ∧ D.toeplitzDet m ≤ 0 := by
  classical
  have hToeplitz := paper_xi_toeplitz_det_verblunsky D
  have hFailureNonempty : ∃ m, m ∈ D.failureSet := by
    rcases hBoundary with ⟨j, hjSteps, hjBad⟩
    exact ⟨j + 1, ⟨j, hjSteps, rfl, hjBad⟩⟩
  let m := Nat.find hFailureNonempty
  have hm : m ∈ D.failureSet := Nat.find_spec hFailureNonempty
  have hLeast : IsLeast D.failureSet m := by
    refine ⟨hm, ?_⟩
    intro r hr
    exact Nat.find_min' hFailureNonempty hr
  have hControl := hToeplitz.2 m hLeast
  exact ⟨hToeplitz.1, hToeplitz.2, ⟨m, hm, hControl.1⟩⟩

end Omega.Zeta
