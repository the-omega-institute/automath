import Mathlib.Tactic

namespace Omega.GroupUnification

/-- Stable words in the terminal window-6 audit sector. -/
abbrev Window6StableWord := Fin 21

/-- The singleton zero sector. -/
def window6ZeroSector : Finset Window6StableWord :=
  ({0} : Finset Window6StableWord)

/-- The eight light words selected by the terminal window-6 split. -/
def window6LightSector : Finset Window6StableWord :=
  ([1, 2, 3, 4, 5, 6, 7, 8] : List Window6StableWord).toFinset

/-- The twelve heavy words selected by the terminal window-6 split. -/
def window6HeavySector : Finset Window6StableWord :=
  ([9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] : List Window6StableWord).toFinset

/-- Paper wrapper for the `1 ⊕ 8 ⊕ 12` terminal window-6 partition.
    prop:terminal-window6-1-8-12-split -/
theorem paper_terminal_window6_1_8_12_split :
    window6ZeroSector.card = 1 ∧
      window6LightSector.card = 8 ∧
      window6HeavySector.card = 12 ∧
      Disjoint window6ZeroSector window6LightSector ∧
      Disjoint window6ZeroSector window6HeavySector ∧
      Disjoint window6LightSector window6HeavySector ∧
      window6ZeroSector ∪ window6LightSector ∪ window6HeavySector = Finset.univ := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, ?_⟩
  ext x
  fin_cases x <;> decide

end Omega.GroupUnification
