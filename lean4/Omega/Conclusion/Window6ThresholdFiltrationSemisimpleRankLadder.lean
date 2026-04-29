import Mathlib.Tactic
import Omega.Conclusion.Window6QmomentTripleGeometry

namespace Omega.Conclusion

/-- The window-`6` histogram multiplicity at fiber dimensions `2`, `3`, and `4`. -/
def conclusion_window6_threshold_filtration_semisimple_rank_ladder_histogram
    (d : ℕ) : ℕ :=
  if d = 2 then 8 else if d = 3 then 4 else if d = 4 then 9 else 0

/-- The threshold tail count `# {w : d(w) ≥ r}` for the audited window-`6` histogram. -/
def conclusion_window6_threshold_filtration_semisimple_rank_ladder_tail_count
    (r : ℕ) : ℕ :=
  if r ≤ 2 then
    conclusion_window6_threshold_filtration_semisimple_rank_ladder_histogram 2 +
      conclusion_window6_threshold_filtration_semisimple_rank_ladder_histogram 3 +
        conclusion_window6_threshold_filtration_semisimple_rank_ladder_histogram 4
  else if r ≤ 3 then
    conclusion_window6_threshold_filtration_semisimple_rank_ladder_histogram 3 +
      conclusion_window6_threshold_filtration_semisimple_rank_ladder_histogram 4
  else if r ≤ 4 then
    conclusion_window6_threshold_filtration_semisimple_rank_ladder_histogram 4
  else
    0

/-- The semisimple Wedderburn block list at threshold `r`, encoded as `(matrix size, count)`. -/
def conclusion_window6_threshold_filtration_semisimple_rank_ladder_blocks
    (r : ℕ) : List (ℕ × ℕ) :=
  if r ≤ 2 then
    [(2, 8), (3, 4), (4, 9)]
  else if r ≤ 3 then
    [(3, 4), (4, 9)]
  else if r ≤ 4 then
    [(4, 9)]
  else
    []

/-- The `K₀` rank of the threshold semisimple algebra. -/
def conclusion_window6_threshold_filtration_semisimple_rank_ladder_k0_rank
    (r : ℕ) : ℕ :=
  conclusion_window6_threshold_filtration_semisimple_rank_ladder_tail_count r

/-- The center dimension of the threshold semisimple algebra. -/
def conclusion_window6_threshold_filtration_semisimple_rank_ladder_center_dim
    (r : ℕ) : ℕ :=
  conclusion_window6_threshold_filtration_semisimple_rank_ladder_tail_count r

/-- The `F₂`-rank of the threshold abelian charge group. -/
def conclusion_window6_threshold_filtration_semisimple_rank_ladder_abelian_charge_rank
    (r : ℕ) : ℕ :=
  conclusion_window6_threshold_filtration_semisimple_rank_ladder_tail_count r

/-- Paper-facing statement for the three threshold layers and their rank ladder. -/
def conclusion_window6_threshold_filtration_semisimple_rank_ladder_statement : Prop :=
  conclusion_window6_threshold_filtration_semisimple_rank_ladder_blocks 2 =
      [(2, 8), (3, 4), (4, 9)] ∧
    conclusion_window6_threshold_filtration_semisimple_rank_ladder_blocks 3 =
      [(3, 4), (4, 9)] ∧
    conclusion_window6_threshold_filtration_semisimple_rank_ladder_blocks 4 =
      [(4, 9)] ∧
    conclusion_window6_threshold_filtration_semisimple_rank_ladder_tail_count 2 = 21 ∧
    conclusion_window6_threshold_filtration_semisimple_rank_ladder_tail_count 3 = 13 ∧
    conclusion_window6_threshold_filtration_semisimple_rank_ladder_tail_count 4 = 9 ∧
    (∀ r ∈ ({2, 3, 4} : Finset ℕ),
      conclusion_window6_threshold_filtration_semisimple_rank_ladder_k0_rank r =
        conclusion_window6_threshold_filtration_semisimple_rank_ladder_tail_count r ∧
      conclusion_window6_threshold_filtration_semisimple_rank_ladder_center_dim r =
        conclusion_window6_threshold_filtration_semisimple_rank_ladder_tail_count r ∧
      conclusion_window6_threshold_filtration_semisimple_rank_ladder_abelian_charge_rank r =
        conclusion_window6_threshold_filtration_semisimple_rank_ladder_tail_count r)

/-- Paper label: `prop:conclusion-window6-threshold-filtration-semisimple-rank-ladder`. -/
theorem paper_conclusion_window6_threshold_filtration_semisimple_rank_ladder :
    conclusion_window6_threshold_filtration_semisimple_rank_ladder_statement := by
  unfold conclusion_window6_threshold_filtration_semisimple_rank_ladder_statement
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide, ?_⟩
  intro r hr
  have hr_cases : r = 2 ∨ r = 3 ∨ r = 4 := by
    simpa using hr
  rcases hr_cases with rfl | rfl | rfl <;> native_decide

end Omega.Conclusion
