import Mathlib.Data.List.Sort
import Mathlib.Tactic

namespace Omega.Zeta

/-- The six prefixed labels for the window-6 `A₂(+)` long-root sector. -/
def xi_window6_a2pm_identical_fiber_spectrum_a2p_sector : List ℕ :=
  [0, 1, 2, 3, 4, 5]

/-- The six prefixed labels for the window-6 `A₂(-)` long-root sector. -/
def xi_window6_a2pm_identical_fiber_spectrum_a2m_sector : List ℕ :=
  [10, 11, 12, 13, 14, 15]

/-- Fiber multiplicity lookup on the prefixed `A₂(±)` finite data. -/
def xi_window6_a2pm_identical_fiber_spectrum_multiplicity : ℕ → ℕ
  | 0 => 4
  | 1 => 4
  | 2 => 3
  | 3 => 3
  | 4 => 2
  | 5 => 2
  | 10 => 4
  | 11 => 4
  | 12 => 3
  | 13 => 3
  | 14 => 2
  | 15 => 2
  | _ => 0

/-- Descending sorted multiplicity spectrum of a finite prefixed sector. -/
def xi_window6_a2pm_identical_fiber_spectrum_sorted (xs : List ℕ) : List ℕ :=
  (xs.map xi_window6_a2pm_identical_fiber_spectrum_multiplicity).insertionSort
    (fun a b : ℕ => b ≤ a)

/-- Sorted spectrum for `A₂(+)`. -/
def xi_window6_a2pm_identical_fiber_spectrum_a2p_sorted : List ℕ :=
  xi_window6_a2pm_identical_fiber_spectrum_sorted
    xi_window6_a2pm_identical_fiber_spectrum_a2p_sector

/-- Sorted spectrum for `A₂(-)`. -/
def xi_window6_a2pm_identical_fiber_spectrum_a2m_sorted : List ℕ :=
  xi_window6_a2pm_identical_fiber_spectrum_sorted
    xi_window6_a2pm_identical_fiber_spectrum_a2m_sector

/-- Paper-facing finite computation: both `A₂(±)` sectors have spectrum `[4,4,3,3,2,2]`. -/
def xi_window6_a2pm_identical_fiber_spectrum_statement : Prop :=
  xi_window6_a2pm_identical_fiber_spectrum_a2p_sorted = [4, 4, 3, 3, 2, 2] ∧
    xi_window6_a2pm_identical_fiber_spectrum_a2m_sorted = [4, 4, 3, 3, 2, 2] ∧
      xi_window6_a2pm_identical_fiber_spectrum_a2p_sorted =
        xi_window6_a2pm_identical_fiber_spectrum_a2m_sorted

/-- Paper label: `thm:xi-window6-a2pm-identical-fiber-spectrum`. -/
theorem paper_xi_window6_a2pm_identical_fiber_spectrum :
    xi_window6_a2pm_identical_fiber_spectrum_statement := by
  unfold xi_window6_a2pm_identical_fiber_spectrum_statement
  unfold xi_window6_a2pm_identical_fiber_spectrum_a2p_sorted
  unfold xi_window6_a2pm_identical_fiber_spectrum_a2m_sorted
  unfold xi_window6_a2pm_identical_fiber_spectrum_sorted
  unfold xi_window6_a2pm_identical_fiber_spectrum_a2p_sector
  unfold xi_window6_a2pm_identical_fiber_spectrum_a2m_sector
  unfold xi_window6_a2pm_identical_fiber_spectrum_multiplicity
  decide

end Omega.Zeta
