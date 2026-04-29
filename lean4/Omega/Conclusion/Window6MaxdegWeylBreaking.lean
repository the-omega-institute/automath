import Mathlib.Tactic
import Omega.Conclusion.Window6ShortLongDegeneracySplitting
import Omega.Conclusion.Window6RootSplitDegeneracyCrossTable

namespace Omega.Conclusion

open Finset

/-- The eighteen non-Cartan root coordinates in the audited window-`6` table. -/
abbrev conclusion_window6_maxdeg_weyl_breaking_rootCoordinate := ℕ

/-- The six short-root coordinates, represented as the first Weyl orbit. -/
def conclusion_window6_maxdeg_weyl_breaking_shortOrbit :
    Finset conclusion_window6_maxdeg_weyl_breaking_rootCoordinate :=
  Finset.range 6

/-- The twelve long-root coordinates, represented as the second Weyl orbit. -/
def conclusion_window6_maxdeg_weyl_breaking_longOrbit :
    Finset conclusion_window6_maxdeg_weyl_breaking_rootCoordinate :=
  Finset.Ico 6 18

/-- The cyclic maximal-degree stratum: five short-root entries and four long-root entries. -/
def conclusion_window6_maxdeg_weyl_breaking_M4 :
    Finset conclusion_window6_maxdeg_weyl_breaking_rootCoordinate :=
  Finset.range 5 ∪ Finset.Ico 6 10

/-- Weyl-invariant finite subsets are unions of the short and long Weyl orbits. -/
def conclusion_window6_maxdeg_weyl_breaking_weylInvariant
    (S : Finset conclusion_window6_maxdeg_weyl_breaking_rootCoordinate) : Prop :=
  ((∀ x, x ∈ conclusion_window6_maxdeg_weyl_breaking_shortOrbit → x ∈ S) ∨
      (∀ x, x ∈ conclusion_window6_maxdeg_weyl_breaking_shortOrbit → x ∉ S)) ∧
    ((∀ x, x ∈ conclusion_window6_maxdeg_weyl_breaking_longOrbit → x ∈ S) ∨
      (∀ x, x ∈ conclusion_window6_maxdeg_weyl_breaking_longOrbit → x ∉ S))

/-- Paper label: `thm:conclusion-window6-maxdeg-weyl-breaking`. -/
theorem paper_conclusion_window6_maxdeg_weyl_breaking :
    conclusion_window6_maxdeg_weyl_breaking_M4.card = 9 ∧
      (conclusion_window6_maxdeg_weyl_breaking_M4 ∩
          conclusion_window6_maxdeg_weyl_breaking_shortOrbit).card = 5 ∧
      (conclusion_window6_maxdeg_weyl_breaking_M4 ∩
          conclusion_window6_maxdeg_weyl_breaking_longOrbit).card = 4 ∧
      ¬ conclusion_window6_maxdeg_weyl_breaking_weylInvariant
          conclusion_window6_maxdeg_weyl_breaking_M4 := by
  have hshort :
      conclusion_window6_maxdeg_weyl_breaking_M4 ∩
          conclusion_window6_maxdeg_weyl_breaking_shortOrbit = Finset.range 5 := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_inter.mp hx with ⟨hxM4, hxShort⟩
      rw [conclusion_window6_maxdeg_weyl_breaking_M4] at hxM4
      rw [conclusion_window6_maxdeg_weyl_breaking_shortOrbit] at hxShort
      rcases Finset.mem_union.mp hxM4 with hxRange | hxIco
      · exact hxRange
      · have hx6 : 6 ≤ x := by
          simpa using (Finset.mem_Ico.mp hxIco).1
        have hxlt6 := Finset.mem_range.mp hxShort
        exact False.elim ((not_lt_of_ge hx6) hxlt6)
    · intro hx
      exact Finset.mem_inter.mpr ⟨by
        rw [conclusion_window6_maxdeg_weyl_breaking_M4]
        exact Finset.mem_union.mpr (Or.inl hx), by
        rw [conclusion_window6_maxdeg_weyl_breaking_shortOrbit]
        exact Finset.mem_range.mpr (Nat.lt_trans (Finset.mem_range.mp hx) (by norm_num))⟩
  have hlong :
      conclusion_window6_maxdeg_weyl_breaking_M4 ∩
          conclusion_window6_maxdeg_weyl_breaking_longOrbit = Finset.Ico 6 10 := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_inter.mp hx with ⟨hxM4, hxLong⟩
      rw [conclusion_window6_maxdeg_weyl_breaking_M4] at hxM4
      rw [conclusion_window6_maxdeg_weyl_breaking_longOrbit] at hxLong
      rcases Finset.mem_union.mp hxM4 with hxRange | hxIco
      · have hxlt5 := Finset.mem_range.mp hxRange
        have hx5 : 6 ≤ x := by
          simpa using (Finset.mem_Ico.mp hxLong).1
        exact False.elim ((not_lt_of_ge hx5) (Nat.lt_trans hxlt5 (by norm_num)))
      · exact hxIco
    · intro hx
      rcases Finset.mem_Ico.mp hx with ⟨hx6, hx10⟩
      exact Finset.mem_inter.mpr ⟨by
        rw [conclusion_window6_maxdeg_weyl_breaking_M4]
        exact Finset.mem_union.mpr (Or.inr hx), by
        rw [conclusion_window6_maxdeg_weyl_breaking_longOrbit]
        exact Finset.mem_Ico.mpr ⟨hx6, Nat.lt_trans hx10 (by norm_num)⟩⟩
  have hdisjoint : Disjoint (Finset.range 5 : Finset ℕ) (Finset.Ico 6 10) := by
    rw [Finset.disjoint_left]
    intro x hxRange hxIco
    simp at hxRange hxIco
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [conclusion_window6_maxdeg_weyl_breaking_M4, Finset.card_union_of_disjoint hdisjoint]
    simp
  · rw [hshort]
    simp
  · rw [hlong]
    simp
  · intro h
    rcases h.1 with hshort | hshort
    · have h5 : (5 : conclusion_window6_maxdeg_weyl_breaking_rootCoordinate) ∈
          conclusion_window6_maxdeg_weyl_breaking_M4 :=
        hshort 5 (by simp [conclusion_window6_maxdeg_weyl_breaking_shortOrbit])
      simp [conclusion_window6_maxdeg_weyl_breaking_M4] at h5
    · have h0 : (0 : conclusion_window6_maxdeg_weyl_breaking_rootCoordinate) ∉
          conclusion_window6_maxdeg_weyl_breaking_M4 :=
        hshort 0 (by simp [conclusion_window6_maxdeg_weyl_breaking_shortOrbit])
      simp [conclusion_window6_maxdeg_weyl_breaking_M4] at h0

end Omega.Conclusion
