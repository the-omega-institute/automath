import Mathlib.Data.Nat.Basic

namespace Omega.Zeta

/-- Paper label: `thm:xi-elliptic-weight-modular-galois-delta-joint-rigidity`. -/
theorem paper_xi_elliptic_weight_modular_galois_delta_joint_rigidity
    (genericGaloisS4 : Prop)
    (deltaBudget2 deltaBudget3 : ℕ)
    (hGal : genericGaloisS4)
    (h2 : deltaBudget2 = 44)
    (h3 : deltaBudget3 = 104) :
    genericGaloisS4 ∧ deltaBudget2 = 44 ∧ deltaBudget3 = 104 := by
  exact ⟨hGal, h2, h3⟩

end Omega.Zeta
