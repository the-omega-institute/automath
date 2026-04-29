import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label:
`cor:xi-time-part63c-window6-schur-packet-locked-by-charpoly`. For the audited window-`6`
multiplicity pattern `(8,4,9)`, the alternating Schur packet is obtained from the characteristic
product by the substitution `z ↦ -z`. -/
theorem paper_xi_time_part63c_window6_schur_packet_locked_by_charpoly :
    let Q6 : ℚ → ℚ := fun z => (1 - 2 * z) ^ 8 * (1 - 3 * z) ^ 4 * (1 - 4 * z) ^ 9
    let E6 : ℚ → ℚ := fun z => (1 + 2 * z) ^ 8 * (1 + 3 * z) ^ 4 * (1 + 4 * z) ^ 9
    ∀ z : ℚ, E6 z = Q6 (-z) := by
  intro Q6 E6 z
  simp [Q6, E6]

end Omega.Zeta
