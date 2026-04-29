import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import Omega.Zeta.XiTimePart9zeNegativeZeroTemperatureFreezing

namespace Omega.Zeta

open scoped BigOperators

/-- The eight-point minimal shell in the negative zero-temperature window-6 certificate. -/
abbrev xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_address := Fin 8

/-- The full minimal shell selected by the negative zero-temperature limit. -/
def xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_minimalShell :
    Finset xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_address :=
  Finset.univ

/-- Boundary addresses inside the minimal shell. -/
def xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_boundaryShell :
    Finset xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_address :=
  Finset.univ.filter fun w => w.val < 3

/-- Interior addresses inside the minimal shell. -/
def xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_interiorShell :
    Finset xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_address :=
  Finset.univ.filter fun w => 3 ≤ w.val

/-- Constant minimal defect on the frozen shell. -/
def xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_defect
    (_w : xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_address) : ℝ :=
  1

/-- The limiting negative zero-temperature law, uniform on the eight minimal addresses. -/
def xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_zeroTempMass
    (w : xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_address) : ℚ :=
  if w ∈ xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_minimalShell then
    1 / 8
  else
    0

/-- Paper-facing finite certificate for the boundary/interior split of the frozen shell. -/
def xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_statement : Prop :=
  xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_minimalShell.card = 8 ∧
    xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_boundaryShell.card = 3 ∧
    xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_interiorShell.card = 5 ∧
    Disjoint
      xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_boundaryShell
      xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_interiorShell ∧
    xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_boundaryShell ∪
        xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_interiorShell =
      xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_minimalShell ∧
    (∀ w ∈ xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_minimalShell,
      xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_defect w = 1) ∧
    (∀ ε > 0, ∃ Q : ℝ, ∀ q ≤ Q,
      |Real.exp (-q * Real.log 1) *
            Finset.sum
              xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_minimalShell
              (fun w =>
                Real.exp
                  (q *
                    Real.log
                      (xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_defect
                        w))) -
          ((xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_minimalShell.filter
              fun w =>
                xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_defect w = 1).card :
            ℝ)| < ε) ∧
    (∑ w ∈ xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_boundaryShell,
        xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_zeroTempMass w) = 3 / 8 ∧
    (∑ w ∈ xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_interiorShell,
        xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_zeroTempMass w) = 5 / 8

/-- Paper label: `thm:xi-time-part9ze-negative-zero-temp-boundary-interior-splitting`. -/
theorem paper_xi_time_part9ze_negative_zero_temp_boundary_interior_splitting :
    xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_statement := by
  have hFreeze :=
    (paper_xi_time_part9ze_negative_zero_temperature_freezing
      xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_minimalShell
      xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_defect
      1
      (by
        simp [xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_minimalShell])
      (by
        intro w hw
        simp [xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_defect])
      (by
        intro w hw
        simp [xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_defect])
      (by
        refine ⟨0, ?_, ?_⟩
        · simp [xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_minimalShell]
        · simp [xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_defect])).2
  have hMinimalCard :
      xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_minimalShell.card = 8 := by
    native_decide
  have hBoundaryCard :
      xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_boundaryShell.card = 3 := by
    native_decide
  have hInteriorCard :
      xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_interiorShell.card = 5 := by
    native_decide
  have hDisjoint :
      Disjoint
        xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_boundaryShell
        xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_interiorShell := by
    native_decide
  have hUnion :
      xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_boundaryShell ∪
          xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_interiorShell =
        xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_minimalShell := by
    native_decide
  have hDefect :
      ∀ w ∈ xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_minimalShell,
        xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_defect w = 1 := by
    intro w hw
    simp [xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_defect]
  have hBoundaryMass :
      (∑ w ∈ xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_boundaryShell,
          xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_zeroTempMass w) =
        3 / 8 := by
    native_decide
  have hInteriorMass :
      (∑ w ∈ xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_interiorShell,
          xi_time_part9ze_negative_zero_temp_boundary_interior_splitting_zeroTempMass w) =
        5 / 8 := by
    native_decide
  exact ⟨hMinimalCard, hBoundaryCard, hInteriorCard, hDisjoint, hUnion, hDefect, hFreeze,
    hBoundaryMass, hInteriorMass⟩

end Omega.Zeta
