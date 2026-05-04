import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-dirichlet-mode-forces-congruence-residual`. -/
theorem paper_xi_dirichlet_mode_forces_congruence_residual
    (m : Nat) (hm : 2 ≤ m)
    (fourierTrace spectralLimsup deviationLowerBound nontrivialModeMax
      sqrtErrorFailure : Prop)
    (hfourier : fourierTrace)
    (hspectral : fourierTrace → spectralLimsup)
    (hdeviation : spectralLimsup → deviationLowerBound)
    (hmax : deviationLowerBound → nontrivialModeMax)
    (hfail : nontrivialModeMax → sqrtErrorFailure) :
    deviationLowerBound ∧ sqrtErrorFailure := by
  have _ : 2 ≤ m := hm
  have hdev : deviationLowerBound := hdeviation (hspectral hfourier)
  exact ⟨hdev, hfail (hmax hdev)⟩

end Omega.Zeta
