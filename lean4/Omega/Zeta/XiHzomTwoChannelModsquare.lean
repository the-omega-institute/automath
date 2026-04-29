import Mathlib.Data.Complex.Basic

namespace Omega.Zeta

open scoped ComplexConjugate

/-- Paper label: `prop:xi-hzom-two-channel-modsquare`. -/
theorem paper_xi_hzom_two_channel_modsquare
    (D Dplus Dminus : ℂ → ℂ)
    (hfactor : ∀ s, D s = Dplus s * Dminus s)
    (hdual : ∀ s, Dminus s = conj (Dplus (1 - conj s)))
    (s : ℂ) (hcrit : 1 - conj s = s) :
    D s = Dplus s * conj (Dplus s) := by
  rw [hfactor s, hdual s, hcrit]

end Omega.Zeta
