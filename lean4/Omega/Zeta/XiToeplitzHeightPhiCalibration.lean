import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-toeplitz-height-phi-calibration`. -/
theorem paper_xi_toeplitz_height_phi_calibration
    (budget : Real → Real) (phi Q N : Real) (m : Nat)
    (hmono : ∀ {a b : Real}, 0 ≤ a → a ≤ b → budget a ≤ budget b) (hQ : 0 ≤ Q)
    (hcal : Q ≤ phi ^ m) (hN : budget (phi ^ m) ≤ N) :
    budget Q ≤ N := by
  exact le_trans (hmono hQ hcal) hN

end Omega.Zeta
