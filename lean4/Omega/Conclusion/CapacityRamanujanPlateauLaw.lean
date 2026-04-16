import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Conclusion.CapacityRamanujanPlateauLaw

open Finset

variable {α : Type*} [Fintype α]

/-- The continuous threshold capacity attached to a finite fiber-size function. -/
def capacityCurve (d : α → ℕ) (s : ℕ) : ℕ :=
  ∑ x, min (d x) s

/-- The discrete capacity increment `Δ C(s) = C(s) - C(s-1)`. -/
def deltaCapacity (d : α → ℕ) (s : ℕ) : ℕ :=
  capacityCurve d s - capacityCurve d (s - 1)

private theorem min_step_indicator (n s : ℕ) (hs : 1 ≤ s) :
    min n s - min n (s - 1) = if s ≤ n then 1 else 0 := by
  by_cases hsn : s ≤ n
  · have hprev : s - 1 ≤ n := by omega
    rw [Nat.min_eq_right hsn, Nat.min_eq_right hprev, if_pos hsn]
    omega
  · have hnlt : n < s := lt_of_not_ge hsn
    have hnle : n ≤ s - 1 := by omega
    rw [Nat.min_eq_left (Nat.le_of_lt hnlt), Nat.min_eq_left hnle, if_neg hsn]
    simp

/-- The jump of the capacity curve counts fibers of size at least `s`. -/
theorem deltaCapacity_eq_card_ge (d : α → ℕ) (s : ℕ) (hs : 1 ≤ s) :
    deltaCapacity d s = Fintype.card {x // s ≤ d x} := by
  classical
  unfold deltaCapacity capacityCurve
  have hle : ∀ x ∈ (Finset.univ : Finset α), min (d x) (s - 1) ≤ min (d x) s := by
    intro x hx
    exact min_le_min_left _ (Nat.sub_le _ _)
  rw [(Finset.sum_tsub_distrib (s := Finset.univ) hle).symm]
  simp_rw [min_step_indicator _ _ hs]
  rw [Fintype.card_of_subtype (Finset.univ.filter fun x => s ≤ d x)]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp

/-- Paper-facing seed package for the Ramanujan plateau law.
    prop:conclusion-capacity-ramanujan-plateau-law -/
theorem paper_conclusion_capacity_ramanujan_plateau_law_seeds
    (d : α → ℕ) (s : ℕ) (hs : 1 ≤ s) :
    deltaCapacity d s = Fintype.card {x // s ≤ d x} ∧
    (0 < deltaCapacity d s ↔ ∃ x, s ≤ d x) ∧
    (deltaCapacity d s = 0 ↔ ∀ x, d x < s) := by
  have hcard := deltaCapacity_eq_card_ge d s hs
  have hpos : 0 < deltaCapacity d s ↔ ∃ x, s ≤ d x := by
    rw [hcard, Fintype.card_pos_iff]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨⟨x, hx⟩⟩
  have hzero : deltaCapacity d s = 0 ↔ ∀ x, d x < s := by
    constructor
    · intro hzero x
      by_contra hx
      have hdelta : 0 < deltaCapacity d s := hpos.mpr ⟨x, le_of_not_gt hx⟩
      omega
    · intro hall
      apply Nat.eq_zero_of_not_pos
      intro hdelta
      rcases hpos.mp hdelta with ⟨x, hx⟩
      exact (not_lt_of_ge hx) (hall x)
  exact ⟨hcard, hpos, hzero⟩

end Omega.Conclusion.CapacityRamanujanPlateauLaw
