import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The concrete window-6 address set used by the finite shell certificate. -/
abbrev xi_time_part9ze_positive_zero_temp_geometric_splitting_address := Fin 21

/-- The multiplicity-four shell selected by positive zero temperature. -/
def xi_time_part9ze_positive_zero_temp_geometric_splitting_maxShell :
    Finset xi_time_part9ze_positive_zero_temp_geometric_splitting_address :=
  Finset.univ.filter fun w => w.val < 9

/-- The four long-root addresses inside the maximal shell. -/
def xi_time_part9ze_positive_zero_temp_geometric_splitting_longShell :
    Finset xi_time_part9ze_positive_zero_temp_geometric_splitting_address :=
  Finset.univ.filter fun w => w.val < 4

/-- The five short-root addresses inside the maximal shell. -/
def xi_time_part9ze_positive_zero_temp_geometric_splitting_shortShell :
    Finset xi_time_part9ze_positive_zero_temp_geometric_splitting_address :=
  Finset.univ.filter fun w => 4 ≤ w.val ∧ w.val < 9

/-- Window-6 multiplicities: nine points of weight `4`, four of weight `3`, and eight of `2`. -/
def xi_time_part9ze_positive_zero_temp_geometric_splitting_multiplicity
    (w : xi_time_part9ze_positive_zero_temp_geometric_splitting_address) : ℕ :=
  if w.val < 9 then 4 else if w.val < 13 then 3 else 2

/-- The positive zero-temperature limiting law, uniform on the multiplicity-four shell. -/
def xi_time_part9ze_positive_zero_temp_geometric_splitting_zeroTempMass
    (w : xi_time_part9ze_positive_zero_temp_geometric_splitting_address) : ℚ :=
  if w ∈ xi_time_part9ze_positive_zero_temp_geometric_splitting_maxShell then 1 / 9 else 0

/-- Paper-facing finite certificate for the window-6 positive zero-temperature split. -/
def xi_time_part9ze_positive_zero_temp_geometric_splitting_statement : Prop :=
  xi_time_part9ze_positive_zero_temp_geometric_splitting_maxShell.card = 9 ∧
    xi_time_part9ze_positive_zero_temp_geometric_splitting_longShell.card = 4 ∧
    xi_time_part9ze_positive_zero_temp_geometric_splitting_shortShell.card = 5 ∧
    Disjoint
      xi_time_part9ze_positive_zero_temp_geometric_splitting_longShell
      xi_time_part9ze_positive_zero_temp_geometric_splitting_shortShell ∧
    xi_time_part9ze_positive_zero_temp_geometric_splitting_longShell ∪
        xi_time_part9ze_positive_zero_temp_geometric_splitting_shortShell =
      xi_time_part9ze_positive_zero_temp_geometric_splitting_maxShell ∧
    (∀ w ∈ xi_time_part9ze_positive_zero_temp_geometric_splitting_maxShell,
      xi_time_part9ze_positive_zero_temp_geometric_splitting_multiplicity w = 4) ∧
    (∀ w, w ∉ xi_time_part9ze_positive_zero_temp_geometric_splitting_maxShell →
      xi_time_part9ze_positive_zero_temp_geometric_splitting_multiplicity w < 4) ∧
    (∀ q : ℕ,
      (∑ w ∈ xi_time_part9ze_positive_zero_temp_geometric_splitting_maxShell,
          xi_time_part9ze_positive_zero_temp_geometric_splitting_multiplicity w ^ q) =
        9 * 4 ^ q) ∧
    (∑ w, xi_time_part9ze_positive_zero_temp_geometric_splitting_zeroTempMass w) = 1 ∧
    (∑ w ∈ xi_time_part9ze_positive_zero_temp_geometric_splitting_longShell,
        xi_time_part9ze_positive_zero_temp_geometric_splitting_zeroTempMass w) = 4 / 9 ∧
    (∑ w ∈ xi_time_part9ze_positive_zero_temp_geometric_splitting_shortShell,
        xi_time_part9ze_positive_zero_temp_geometric_splitting_zeroTempMass w) = 5 / 9

/-- Paper label: `thm:xi-time-part9ze-positive-zero-temp-geometric-splitting`. -/
theorem paper_xi_time_part9ze_positive_zero_temp_geometric_splitting :
    xi_time_part9ze_positive_zero_temp_geometric_splitting_statement := by
  have hMaxCard :
      xi_time_part9ze_positive_zero_temp_geometric_splitting_maxShell.card = 9 := by
    native_decide
  have hLongCard :
      xi_time_part9ze_positive_zero_temp_geometric_splitting_longShell.card = 4 := by
    native_decide
  have hShortCard :
      xi_time_part9ze_positive_zero_temp_geometric_splitting_shortShell.card = 5 := by
    native_decide
  have hDisjoint :
      Disjoint
        xi_time_part9ze_positive_zero_temp_geometric_splitting_longShell
        xi_time_part9ze_positive_zero_temp_geometric_splitting_shortShell := by
    native_decide
  have hUnion :
      xi_time_part9ze_positive_zero_temp_geometric_splitting_longShell ∪
          xi_time_part9ze_positive_zero_temp_geometric_splitting_shortShell =
        xi_time_part9ze_positive_zero_temp_geometric_splitting_maxShell := by
    native_decide
  have hMaxMultiplicity :
      ∀ w ∈ xi_time_part9ze_positive_zero_temp_geometric_splitting_maxShell,
        xi_time_part9ze_positive_zero_temp_geometric_splitting_multiplicity w = 4 := by
    native_decide
  have hOffMax :
      ∀ w, w ∉ xi_time_part9ze_positive_zero_temp_geometric_splitting_maxShell →
        xi_time_part9ze_positive_zero_temp_geometric_splitting_multiplicity w < 4 := by
    native_decide
  have hPower :
      ∀ q : ℕ,
        (∑ w ∈ xi_time_part9ze_positive_zero_temp_geometric_splitting_maxShell,
            xi_time_part9ze_positive_zero_temp_geometric_splitting_multiplicity w ^ q) =
          9 * 4 ^ q := by
    intro q
    calc
      (∑ w ∈ xi_time_part9ze_positive_zero_temp_geometric_splitting_maxShell,
          xi_time_part9ze_positive_zero_temp_geometric_splitting_multiplicity w ^ q)
          = ∑ w ∈ xi_time_part9ze_positive_zero_temp_geometric_splitting_maxShell,
              4 ^ q := by
            refine Finset.sum_congr rfl ?_
            intro w hw
            rw [hMaxMultiplicity w hw]
      _ = 9 * 4 ^ q := by
            simp [hMaxCard]
  have hTotalMass :
      (∑ w, xi_time_part9ze_positive_zero_temp_geometric_splitting_zeroTempMass w) = 1 := by
    native_decide
  have hLongMass :
      (∑ w ∈ xi_time_part9ze_positive_zero_temp_geometric_splitting_longShell,
          xi_time_part9ze_positive_zero_temp_geometric_splitting_zeroTempMass w) = 4 / 9 := by
    native_decide
  have hShortMass :
      (∑ w ∈ xi_time_part9ze_positive_zero_temp_geometric_splitting_shortShell,
          xi_time_part9ze_positive_zero_temp_geometric_splitting_zeroTempMass w) = 5 / 9 := by
    native_decide
  exact ⟨hMaxCard, hLongCard, hShortCard, hDisjoint, hUnion, hMaxMultiplicity, hOffMax,
    hPower, hTotalMass, hLongMass, hShortMass⟩

end Omega.Zeta
