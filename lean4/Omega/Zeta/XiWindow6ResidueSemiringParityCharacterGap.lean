import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-window6-residue-semiring-parity-character-gap`. -/
theorem paper_xi_window6_residue_semiring_parity_character_gap
    {ParityCharacters Residue : Type*} [Fintype ParityCharacters] [Fintype Residue]
    (hchars : Fintype.card ParityCharacters = 2 ^ 21) (hresidue : Fintype.card Residue = 21) :
    ¬ ∃ f : ParityCharacters → Residue, Function.Injective f := by
  rintro ⟨f, hf⟩
  have hle := Fintype.card_le_of_injective f hf
  rw [hchars, hresidue] at hle
  norm_num at hle

end Omega.Zeta
