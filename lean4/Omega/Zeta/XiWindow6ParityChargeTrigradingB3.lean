import Mathlib.Tactic
import Omega.Zeta.XiWindow6B3C3TightFrameFourthMomentNonsimilarity

namespace Omega.Zeta

/-- Concrete data token for the window-`6` `B₃` parity/charge trigrading audit. -/
abbrev xi_window6_parity_charge_trigrading_b3_data :=
  Unit

namespace xi_window6_parity_charge_trigrading_b3_data

/-- The three axis labels which form the charge-free anchor part of the trigrading. -/
def xi_window6_parity_charge_trigrading_b3_axisLabels
    (_D : xi_window6_parity_charge_trigrading_b3_data) : List (Fin 3) :=
  [0, 1, 2]

/-- The parity orbit is the six short roots of the concrete `B₃` dictionary. -/
def xi_window6_parity_charge_trigrading_b3_parityRoots
    (_D : xi_window6_parity_charge_trigrading_b3_data) : List XiWindow6Root :=
  xiWindow6B3ShortRoots

/-- The charge orbit is the twelve long roots `±eᵢ ± eⱼ` carried by the same dictionary. -/
def xi_window6_parity_charge_trigrading_b3_chargeRoots
    (_D : xi_window6_parity_charge_trigrading_b3_data) : List XiWindow6Root :=
  xiWindow6ShortRoots

/-- The finite window-`6` split has cardinalities `3`, `6`, and `12`. -/
def cardinality_split (D : xi_window6_parity_charge_trigrading_b3_data) : Prop :=
  D.xi_window6_parity_charge_trigrading_b3_axisLabels.length = 3 ∧
    D.xi_window6_parity_charge_trigrading_b3_parityRoots.length = 6 ∧
      D.xi_window6_parity_charge_trigrading_b3_chargeRoots.length = 12

/-- The parity and charge pieces assemble with the three anchors to the full `21`-slot grading. -/
def parity_charge_trigrading (D : xi_window6_parity_charge_trigrading_b3_data) : Prop :=
  D.xi_window6_parity_charge_trigrading_b3_axisLabels.length +
      D.xi_window6_parity_charge_trigrading_b3_parityRoots.length +
        D.xi_window6_parity_charge_trigrading_b3_chargeRoots.length = 21 ∧
    D.xi_window6_parity_charge_trigrading_b3_parityRoots ++
        D.xi_window6_parity_charge_trigrading_b3_chargeRoots =
      xiWindow6B3Roots

end xi_window6_parity_charge_trigrading_b3_data

open xi_window6_parity_charge_trigrading_b3_data

/-- Paper label: `thm:xi-window6-parity-charge-trigrading-b3`. -/
theorem paper_xi_window6_parity_charge_trigrading_b3
    (D : xi_window6_parity_charge_trigrading_b3_data) :
    D.cardinality_split ∧ D.parity_charge_trigrading := by
  simp [cardinality_split, parity_charge_trigrading,
    xi_window6_parity_charge_trigrading_b3_axisLabels,
    xi_window6_parity_charge_trigrading_b3_parityRoots,
    xi_window6_parity_charge_trigrading_b3_chargeRoots,
    xiWindow6B3Roots, xiWindow6B3ShortRoots, xiWindow6ShortRoots]

end Omega.Zeta
