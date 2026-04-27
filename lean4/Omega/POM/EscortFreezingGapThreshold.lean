import Mathlib.Tactic

open Finset
open scoped BigOperators

namespace Omega.POM

/-- Concrete finite data for the max-fiber escort mass and off-maximal gap estimate.

Paper label: `prop:pom-escort-freezing-gap-threshold`. -/
structure pom_escort_freezing_gap_threshold_data where
  X : Type
  instFintype : Fintype X
  instDecidableEq : DecidableEq X
  d : X → ℝ
  maxSet : Finset X
  q : ℕ
  M : ℝ
  M2 : ℝ
  S : ℝ
  S_def : S = ∑ x : X, d x ^ q
  max_value : ∀ x, x ∈ maxSet → d x = M
  off_le_second : ∀ x, x ∉ maxSet → d x ^ q ≤ M2 ^ q
  second_power_nonneg : 0 ≤ M2 ^ q
  S_pos : 0 < S

namespace pom_escort_freezing_gap_threshold_data

/-- The concrete conclusion: exact mass on the maximal layer, plus the standard finite
second-layer upper bound for the missing escort mass. -/
def pom_escort_freezing_gap_threshold_conclusion
    (D : pom_escort_freezing_gap_threshold_data) : Prop :=
  letI : Fintype D.X := D.instFintype
  letI : DecidableEq D.X := D.instDecidableEq
  ((D.maxSet.sum fun x => D.d x ^ D.q) / D.S =
      (D.maxSet.card : ℝ) * D.M ^ D.q / D.S) ∧
    (1 - ((D.maxSet.sum fun x => D.d x ^ D.q) / D.S) ≤
      (((Finset.univ.filter (fun x : D.X => x ∉ D.maxSet)).sum fun x => D.d x ^ D.q) /
        D.S)) ∧
    (((Finset.univ.filter (fun x : D.X => x ∉ D.maxSet)).sum fun x => D.d x ^ D.q) /
        D.S ≤ (Fintype.card D.X : ℝ) * D.M2 ^ D.q / D.S)

end pom_escort_freezing_gap_threshold_data

/-- Paper label: `prop:pom-escort-freezing-gap-threshold`. -/
theorem paper_pom_escort_freezing_gap_threshold
    (D : pom_escort_freezing_gap_threshold_data) :
    D.pom_escort_freezing_gap_threshold_conclusion := by
  letI : Fintype D.X := D.instFintype
  letI : DecidableEq D.X := D.instDecidableEq
  dsimp [pom_escort_freezing_gap_threshold_data.pom_escort_freezing_gap_threshold_conclusion]
  let A : ℝ := D.maxSet.sum fun x => D.d x ^ D.q
  let B : ℝ := (Finset.univ.filter (fun x : D.X => x ∉ D.maxSet)).sum fun x =>
    D.d x ^ D.q
  have hA : A = (D.maxSet.card : ℝ) * D.M ^ D.q := by
    dsimp [A]
    calc
      D.maxSet.sum (fun x => D.d x ^ D.q) = D.maxSet.sum (fun _x => D.M ^ D.q) := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        rw [D.max_value x hx]
      _ = (D.maxSet.card : ℝ) * D.M ^ D.q := by simp [mul_comm]
  have hS_split : D.S = A + B := by
    dsimp [A, B]
    rw [D.S_def]
    symm
    calc
      D.maxSet.sum (fun x => D.d x ^ D.q) +
          ((Finset.univ.filter (fun x : D.X => x ∉ D.maxSet)).sum fun x => D.d x ^ D.q)
          = (D.maxSet ∪ (Finset.univ.filter (fun x : D.X => x ∉ D.maxSet))).sum
              (fun x => D.d x ^ D.q) := by
            rw [Finset.sum_union]
            exact Finset.disjoint_left.mpr (by
              intro x hxmax hxoff
              exact (Finset.mem_filter.mp hxoff).2 hxmax)
      _ = ∑ x : D.X, D.d x ^ D.q := by
        refine Finset.sum_congr ?_ (fun x _ => rfl)
        ext x
        constructor
        · intro hx
          exact Finset.mem_univ x
        · intro _hx
          by_cases hxmax : x ∈ D.maxSet
          · exact Finset.mem_union_left _ hxmax
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxmax⟩)
  have hfirst : A / D.S = (D.maxSet.card : ℝ) * D.M ^ D.q / D.S := by
    rw [hA]
  have hmissing : 1 - A / D.S ≤ B / D.S := by
    have hSne : D.S ≠ 0 := ne_of_gt D.S_pos
    calc
      1 - A / D.S = (D.S - A) / D.S := by field_simp [hSne]
      _ = B / D.S := by rw [hS_split]; ring
      _ ≤ B / D.S := le_rfl
  have hB_le : B ≤ (Fintype.card D.X : ℝ) * D.M2 ^ D.q := by
    calc
      B ≤ (Finset.univ.filter (fun x : D.X => x ∉ D.maxSet)).sum
          (fun _x => D.M2 ^ D.q) := by
        dsimp [B]
        refine Finset.sum_le_sum ?_
        intro x hx
        exact D.off_le_second x (Finset.mem_filter.mp hx).2
      _ = (((Finset.univ.filter (fun x : D.X => x ∉ D.maxSet)).card : ℝ) *
          D.M2 ^ D.q) := by
        simp [mul_comm]
      _ ≤ (Fintype.card D.X : ℝ) * D.M2 ^ D.q := by
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast
            (Finset.card_filter_le Finset.univ (fun x : D.X => x ∉ D.maxSet)))
          D.second_power_nonneg
  have hthird : B / D.S ≤ (Fintype.card D.X : ℝ) * D.M2 ^ D.q / D.S := by
    exact div_le_div_of_nonneg_right hB_le (le_of_lt D.S_pos)
  exact ⟨hfirst, hmissing, hthird⟩

end Omega.POM
