import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-hellinger-charge-potential-duality-dtn`. The finite Green-kernel
formulation is ordinary matrix algebra: the potential is `G.mulVec`, the energy is its quadratic
pairing with the charge vector, and the two inverse hypotheses identify the unique charge
realizing each potential vector. -/
theorem paper_xi_hellinger_charge_potential_duality_dtn {κ : ℕ}
    (G Ginv : Matrix (Fin κ) (Fin κ) ℝ) (energy : (Fin κ → ℝ) → ℝ)
    (potential : (Fin κ → ℝ) → Fin κ → ℝ)
    (hEnergy : ∀ c, energy c = ∑ i, c i * potential c i)
    (hPotential : ∀ c, potential c = G.mulVec c)
    (hLeftInv : ∀ v, G.mulVec (Ginv.mulVec v) = v)
    (hRightInv : ∀ c, Ginv.mulVec (G.mulVec c) = c) :
    (∀ c, energy c = ∑ i, c i * (G.mulVec c) i) ∧
      (∀ v, (∃! c, G.mulVec c = v) ∧
        energy (Ginv.mulVec v) = ∑ i, v i * (Ginv.mulVec v) i) := by
  have hEnergyMatrix : ∀ c, energy c = ∑ i, c i * (G.mulVec c) i := by
    intro c
    rw [hEnergy c, hPotential c]
  refine ⟨hEnergyMatrix, ?_⟩
  intro v
  constructor
  · refine ⟨Ginv.mulVec v, hLeftInv v, ?_⟩
    intro c hc
    have hrecover : Ginv.mulVec v = c := by
      calc
        Ginv.mulVec v = Ginv.mulVec (G.mulVec c) := by rw [hc]
        _ = c := hRightInv c
    exact hrecover.symm
  · calc
      energy (Ginv.mulVec v) =
          ∑ i, (Ginv.mulVec v) i * (G.mulVec (Ginv.mulVec v)) i :=
        hEnergyMatrix (Ginv.mulVec v)
      _ = ∑ i, (Ginv.mulVec v) i * v i := by rw [hLeftInv v]
      _ = ∑ i, v i * (Ginv.mulVec v) i := by simp [mul_comm]

end Omega.Zeta
