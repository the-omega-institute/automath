import Mathlib.Data.Complex.Basic
import Omega.Zeta.AbelChannelEquipartitionCharacter

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Paper label: `prop:abel-cyclic-character-projection`. In the concrete cyclic-channel model,
vanishing of all nonzero character coefficients is exactly the statement that the finite Fourier
projection onto the zero mode recovers the whole residue profile. -/
theorem paper_abel_cyclic_character_projection (m : ℕ) (hm : 2 ≤ m) :
    ∀ w : Fin m → ℂ,
      (∀ a : Fin m,
        abel_channel_equipartition_character_nontrivial a →
          abel_channel_equipartition_character_fourier_coeff w a = 0) ↔
        ∀ j : Fin m, w j = (∑ i, w i) / m := by
  intro w
  simpa using paper_abel_channel_equipartition_character m hm w

end

end Omega.Zeta
