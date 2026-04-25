import Mathlib.Data.Fintype.Card

namespace Omega.GU

/-- Paper label: `cor:bdry-sheet-parity-extension-min-register`.
Any deterministic register that distinguishes the three sheet-parity extension choices has at
least three states. -/
theorem paper_bdry_sheet_parity_extension_min_register {R : Type} [Fintype R]
    (encode : Fin 3 → R) (hinj : Function.Injective encode) : 3 ≤ Fintype.card R := by
  simpa [Fintype.card_fin] using Fintype.card_le_of_injective encode hinj

end Omega.GU
