import Mathlib.Tactic

namespace Omega.GU.Window6B3SupportCount

open Finset

/-- Ternary set `{-1, 0, 1}`.
    thm:window6-b3-support-vanishing-ideal-hilbert -/
def ternarySet : Finset ℤ := {-1, 0, 1}

/-- The 27-point cube `{-1, 0, 1}^3`.
    thm:window6-b3-support-vanishing-ideal-hilbert -/
def cube27 : Finset (ℤ × ℤ × ℤ) := ternarySet ×ˢ ternarySet ×ˢ ternarySet

/-- Subset where at least one coordinate is zero (vanishing ideal support).
    thm:window6-b3-support-vanishing-ideal-hilbert -/
def supportZero : Finset (ℤ × ℤ × ℤ) :=
  cube27.filter (fun p => p.1 = 0 ∨ p.2.1 = 0 ∨ p.2.2 = 0)

/-- Subset where all coordinates are nonzero.
    thm:window6-b3-support-vanishing-ideal-hilbert -/
def supportNonzero : Finset (ℤ × ℤ × ℤ) :=
  cube27.filter (fun p => p.1 ≠ 0 ∧ p.2.1 ≠ 0 ∧ p.2.2 ≠ 0)

/-- The cube has 27 elements.
    thm:window6-b3-support-vanishing-ideal-hilbert -/
theorem cube27_card : cube27.card = 27 := by decide

/-- The all-nonzero subset has 8 elements.
    thm:window6-b3-support-vanishing-ideal-hilbert -/
theorem supportNonzero_card : supportNonzero.card = 8 := by decide

/-- The two filters are disjoint.
    thm:window6-b3-support-vanishing-ideal-hilbert -/
theorem supportZero_disjoint_nonzero : Disjoint supportZero supportNonzero := by
  unfold supportZero supportNonzero
  rw [Finset.disjoint_filter]
  intro p _ hzero hnz
  rcases hzero with h1 | h2 | h3
  · exact hnz.1 h1
  · exact hnz.2.1 h2
  · exact hnz.2.2 h3

/-- The two filters cover the cube.
    thm:window6-b3-support-vanishing-ideal-hilbert -/
theorem supportZero_union_nonzero : supportZero ∪ supportNonzero = cube27 := by
  unfold supportZero supportNonzero
  ext p
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨hcube, _⟩ | ⟨hcube, _⟩) <;> exact hcube
  · intro hcube
    by_cases h1 : p.1 = 0
    · exact Or.inl ⟨hcube, Or.inl h1⟩
    · by_cases h2 : p.2.1 = 0
      · exact Or.inl ⟨hcube, Or.inr (Or.inl h2)⟩
      · by_cases h3 : p.2.2 = 0
        · exact Or.inl ⟨hcube, Or.inr (Or.inr h3)⟩
        · exact Or.inr ⟨hcube, h1, h2, h3⟩

/-- The vanishing-ideal support has 19 elements: 27 - 8.
    thm:window6-b3-support-vanishing-ideal-hilbert -/
theorem supportZero_card : supportZero.card = 19 := by
  have hunion := supportZero_union_nonzero
  have hdisj := supportZero_disjoint_nonzero
  have hsum : (supportZero ∪ supportNonzero).card =
      supportZero.card + supportNonzero.card :=
    Finset.card_union_of_disjoint hdisj
  rw [hunion] at hsum
  rw [cube27_card, supportNonzero_card] at hsum
  omega

/-- Paper package: window-6 B₃ support count = 27 - 8 = 19.
    thm:window6-b3-support-vanishing-ideal-hilbert -/
theorem paper_window6_b3_support_count : supportZero.card = 27 - 8 := by
  rw [supportZero_card]

end Omega.GU.Window6B3SupportCount
