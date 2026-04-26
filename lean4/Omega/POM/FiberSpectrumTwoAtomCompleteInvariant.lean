import Omega.POM.FiberSpectrumFiniteReconstructionSharp

namespace Omega.POM

/-- Paper label: `cor:pom-fiber-spectrum-two-atom-complete-invariant`. The sharp finite
reconstruction theorem specializes the `2R` window to `4` when the atom count is exactly `2`,
while the Prony/Hankel rank package remains the complete-invariant witness. -/
theorem paper_pom_fiber_spectrum_two_atom_complete_invariant
    (D : FiberSpectrumPronyHankelRankData) (h2 : D.atomCount = 2) :
    pom_fiber_spectrum_finite_reconstruction_sharp_window D.atomCount = 4 ∧
      pom_fiber_spectrum_finite_reconstruction_sharp_reconstructs D := by
  rcases paper_pom_fiber_spectrum_finite_reconstruction_sharp D (by simp [h2]) with
    ⟨hwindow, hreconstruct, _, _⟩
  refine ⟨?_, hreconstruct⟩
  calc
    pom_fiber_spectrum_finite_reconstruction_sharp_window D.atomCount = 2 * D.atomCount := hwindow
    _ = 4 := by simp [h2]

end Omega.POM
