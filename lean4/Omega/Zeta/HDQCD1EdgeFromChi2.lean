import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-hdqcd1-edge-from-chi2`. -/
theorem paper_xi_hdqcd1_edge_from_chi2 (N chi C hN : ℝ) (hchi : chi ≠ 0)
    (hhN : hN ≠ 0) (hden : C + 2 * hN ≠ 0)
    (hchi_eq : chi = (2 * hN * N ^ 2) / (C + 2 * hN)) :
    C / (2 * hN) = N ^ 2 / chi - 1 := by
  have htwohN : 2 * hN ≠ 0 := mul_ne_zero two_ne_zero hhN
  have hclear : chi * (C + 2 * hN) = 2 * hN * N ^ 2 := by
    rw [hchi_eq]
    field_simp [hden]
  field_simp [htwohN, hchi]
  nlinarith

end Omega.Zeta
