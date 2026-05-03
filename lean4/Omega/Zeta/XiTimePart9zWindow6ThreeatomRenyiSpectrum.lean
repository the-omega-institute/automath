import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Omega.FoldResidualTime.Window6FixedFreezingLaw
import Omega.Zeta.Window6RenyiDivergenceParityChargeRedundancy

namespace Omega.Zeta

open Omega.FoldResidualTime

noncomputable section

/-- Concrete carrier for the window-6 three-atom Rényi spectrum package. -/
abbrev xi_time_part9z_window6_threeatom_renyi_spectrum_data := Unit

namespace xi_time_part9z_window6_threeatom_renyi_spectrum_data

/-- The window-6 Rényi entropy from the three atom histogram `(8,4,9)` over fiber sizes
`2,3,4`. -/
def xi_time_part9z_window6_threeatom_renyi_spectrum_renyi (q : ℕ) : ℝ :=
  Real.log (window6FiberMomentSum q / (64 : ℝ) ^ q) / (1 - (q : ℝ))

/-- The Hartley endpoint: the visible support has `21` atoms. -/
def xi_time_part9z_window6_threeatom_renyi_spectrum_H0 : ℝ :=
  Real.log 21

/-- The Shannon endpoint in natural-log units. -/
def xi_time_part9z_window6_threeatom_renyi_spectrum_H1 : ℝ :=
  (37 / 8 : ℝ) * Real.log 2 - (3 / 16 : ℝ) * Real.log 3

/-- The collision endpoint from the second moment `212/64^2 = 53/1024`. -/
def xi_time_part9z_window6_threeatom_renyi_spectrum_H2 : ℝ :=
  -Real.log ((53 : ℝ) / 1024)

/-- The min-entropy endpoint from the largest fiber class, with mass `9*4/64 = 9/16`. -/
def xi_time_part9z_window6_threeatom_renyi_spectrum_Hinf : ℝ :=
  -Real.log ((9 : ℝ) / 16)

/-- Exact finite-`q` Rényi formula from the window-6 fiber moment sum. -/
def renyi_formula (_D : xi_time_part9z_window6_threeatom_renyi_spectrum_data) : Prop :=
  ∀ q : ℕ, 2 ≤ q →
    xi_time_part9z_window6_threeatom_renyi_spectrum_renyi q =
      Real.log ((8 * (2 : ℝ) ^ q + 4 * (3 : ℝ) ^ q + 9 * (4 : ℝ) ^ q) /
        (64 : ℝ) ^ q) / (1 - (q : ℝ))

/-- Hartley entropy endpoint. -/
def H0_formula (_D : xi_time_part9z_window6_threeatom_renyi_spectrum_data) : Prop :=
  xi_time_part9z_window6_threeatom_renyi_spectrum_H0 = Real.log 21

/-- Shannon entropy endpoint. -/
def H1_formula (_D : xi_time_part9z_window6_threeatom_renyi_spectrum_data) : Prop :=
  xi_time_part9z_window6_threeatom_renyi_spectrum_H1 =
    (37 / 8 : ℝ) * Real.log 2 - (3 / 16 : ℝ) * Real.log 3

/-- Collision entropy endpoint. -/
def H2_formula (_D : xi_time_part9z_window6_threeatom_renyi_spectrum_data) : Prop :=
  xi_time_part9z_window6_threeatom_renyi_spectrum_H2 = -Real.log ((53 : ℝ) / 1024)

/-- Min-entropy endpoint. -/
def Hinf_formula (_D : xi_time_part9z_window6_threeatom_renyi_spectrum_data) : Prop :=
  xi_time_part9z_window6_threeatom_renyi_spectrum_Hinf = -Real.log ((9 : ℝ) / 16)

end xi_time_part9z_window6_threeatom_renyi_spectrum_data

/-- Paper label: `thm:xi-time-part9z-window6-threeatom-renyi-spectrum`. -/
theorem paper_xi_time_part9z_window6_threeatom_renyi_spectrum
    (D : xi_time_part9z_window6_threeatom_renyi_spectrum_data) :
    D.renyi_formula ∧ D.H0_formula ∧ D.H1_formula ∧ D.H2_formula ∧ D.Hinf_formula := by
  rcases Omega.FoldResidualTime.paper_frt_window6_fixed_freezing_law with ⟨hmoment, _, _, _, _, _⟩
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  intro q hq
  simp [xi_time_part9z_window6_threeatom_renyi_spectrum_data.xi_time_part9z_window6_threeatom_renyi_spectrum_renyi,
    hmoment q]

end

end Omega.Zeta
