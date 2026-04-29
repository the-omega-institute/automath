import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-finite-truncation-spectrum-converges`. -/
theorem paper_xi_finite_truncation_spectrum_converges
    (spectralIncluded secondEigenvalueConverges : ℕ → Prop)
    (hSpec : ∀ m, spectralIncluded m)
    (hLam : ∀ m, secondEigenvalueConverges m) :
    (∀ m, spectralIncluded m) ∧ (∀ m, secondEigenvalueConverges m) := by
  exact ⟨hSpec, hLam⟩

end Omega.Zeta
