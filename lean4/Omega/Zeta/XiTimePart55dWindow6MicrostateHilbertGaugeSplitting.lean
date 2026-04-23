import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic
import Omega.Folding.BinFold

namespace Omega.Zeta

/-- Visible sector: one constant vector for each window-`6` fiber. -/
abbrev xi_time_part55d_window6_microstate_hilbert_gauge_splitting_visible_sector := Fin 21

/-- Hidden `Std₄` packet: the nine `d = 4` fibers contribute `9 * (4 - 1) = 27` dimensions. -/
abbrev xi_time_part55d_window6_microstate_hilbert_gauge_splitting_std4_sector := Fin 27

/-- Hidden `Std₃` packet: the four `d = 3` fibers contribute `4 * (3 - 1) = 8` dimensions. -/
abbrev xi_time_part55d_window6_microstate_hilbert_gauge_splitting_std3_sector := Fin 8

/-- Hidden `sgn₂` packet: the eight `d = 2` fibers contribute `8 * (2 - 1) = 8` dimensions. -/
abbrev xi_time_part55d_window6_microstate_hilbert_gauge_splitting_sgn2_sector := Fin 8

/-- Total hidden sector dimension. -/
abbrev xi_time_part55d_window6_microstate_hilbert_gauge_splitting_hidden_sector := Fin 43

/-- Full microstate space dimension. -/
abbrev xi_time_part55d_window6_microstate_hilbert_gauge_splitting_microstate_sector := Fin 64

/-- Concrete dimension bookkeeping for the window-`6` visible/hidden Hilbert splitting. -/
def xi_time_part55d_window6_microstate_hilbert_gauge_splitting_statement : Prop :=
  Fintype.card xi_time_part55d_window6_microstate_hilbert_gauge_splitting_visible_sector =
      cBinFiberHist 6 2 + cBinFiberHist 6 3 + cBinFiberHist 6 4 ∧
    Fintype.card xi_time_part55d_window6_microstate_hilbert_gauge_splitting_std4_sector =
      cBinFiberHist 6 4 * (4 - 1) ∧
    Fintype.card xi_time_part55d_window6_microstate_hilbert_gauge_splitting_std3_sector =
      cBinFiberHist 6 3 * (3 - 1) ∧
    Fintype.card xi_time_part55d_window6_microstate_hilbert_gauge_splitting_sgn2_sector =
      cBinFiberHist 6 2 * (2 - 1) ∧
    Fintype.card xi_time_part55d_window6_microstate_hilbert_gauge_splitting_hidden_sector = 43 ∧
    Fintype.card xi_time_part55d_window6_microstate_hilbert_gauge_splitting_hidden_sector =
      Fintype.card xi_time_part55d_window6_microstate_hilbert_gauge_splitting_std4_sector +
        Fintype.card xi_time_part55d_window6_microstate_hilbert_gauge_splitting_std3_sector +
        Fintype.card xi_time_part55d_window6_microstate_hilbert_gauge_splitting_sgn2_sector ∧
    Fintype.card xi_time_part55d_window6_microstate_hilbert_gauge_splitting_microstate_sector =
      Fintype.card xi_time_part55d_window6_microstate_hilbert_gauge_splitting_visible_sector +
        Fintype.card xi_time_part55d_window6_microstate_hilbert_gauge_splitting_hidden_sector

/-- Paper label: `thm:xi-time-part55d-window6-microstate-hilbert-gauge-splitting`. -/
theorem paper_xi_time_part55d_window6_microstate_hilbert_gauge_splitting :
    xi_time_part55d_window6_microstate_hilbert_gauge_splitting_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cBinFiberHist_6_2, cBinFiberHist_6_3, cBinFiberHist_6_4]
    norm_num [xi_time_part55d_window6_microstate_hilbert_gauge_splitting_visible_sector]
  · rw [cBinFiberHist_6_4]
    norm_num [xi_time_part55d_window6_microstate_hilbert_gauge_splitting_std4_sector]
  · rw [cBinFiberHist_6_3]
    norm_num [xi_time_part55d_window6_microstate_hilbert_gauge_splitting_std3_sector]
  · rw [cBinFiberHist_6_2]
    norm_num [xi_time_part55d_window6_microstate_hilbert_gauge_splitting_sgn2_sector]
  · norm_num [xi_time_part55d_window6_microstate_hilbert_gauge_splitting_hidden_sector]
  · norm_num [xi_time_part55d_window6_microstate_hilbert_gauge_splitting_hidden_sector,
      xi_time_part55d_window6_microstate_hilbert_gauge_splitting_std4_sector,
      xi_time_part55d_window6_microstate_hilbert_gauge_splitting_std3_sector,
      xi_time_part55d_window6_microstate_hilbert_gauge_splitting_sgn2_sector]
  · norm_num [xi_time_part55d_window6_microstate_hilbert_gauge_splitting_microstate_sector,
      xi_time_part55d_window6_microstate_hilbert_gauge_splitting_visible_sector,
      xi_time_part55d_window6_microstate_hilbert_gauge_splitting_hidden_sector]

end Omega.Zeta
