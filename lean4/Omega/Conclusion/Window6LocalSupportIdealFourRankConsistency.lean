import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite-support data for a window-`6` local support ideal. -/
structure conclusion_window6_local_support_ideal_four_rank_consistency_data where
  conclusion_window6_local_support_ideal_four_rank_consistency_support : Finset (Fin 21)
  conclusion_window6_local_support_ideal_four_rank_consistency_fiber_size : Fin 21 → ℕ
  conclusion_window6_local_support_ideal_four_rank_consistency_fiber_size_mem :
    ∀ y,
      y ∈ conclusion_window6_local_support_ideal_four_rank_consistency_support →
        conclusion_window6_local_support_ideal_four_rank_consistency_fiber_size y = 2 ∨
          conclusion_window6_local_support_ideal_four_rank_consistency_fiber_size y = 3 ∨
            conclusion_window6_local_support_ideal_four_rank_consistency_fiber_size y = 4

/-- The allowed window-`6` fiber sizes. -/
def conclusion_window6_local_support_ideal_four_rank_consistency_window6_size
    (d : ℕ) : Prop :=
  d = 2 ∨ d = 3 ∨ d = 4

/-- One simple block contributes one central idempotent. -/
def conclusion_window6_local_support_ideal_four_rank_consistency_center_dim
    (D : conclusion_window6_local_support_ideal_four_rank_consistency_data) : ℕ :=
  D.conclusion_window6_local_support_ideal_four_rank_consistency_support.card

/-- One matrix block contributes one copy of `K_0(M_n(C)) ≃ Z`. -/
def conclusion_window6_local_support_ideal_four_rank_consistency_k0_rank
    (D : conclusion_window6_local_support_ideal_four_rank_consistency_data) : ℕ :=
  D.conclusion_window6_local_support_ideal_four_rank_consistency_support.card

/-- For fiber sizes `2,3,4`, each symmetric factor contributes one sign coordinate. -/
def conclusion_window6_local_support_ideal_four_rank_consistency_abelian_rank
    (D : conclusion_window6_local_support_ideal_four_rank_consistency_data) : ℕ :=
  D.conclusion_window6_local_support_ideal_four_rank_consistency_support.card

/-- The finite support count. -/
def conclusion_window6_local_support_ideal_four_rank_consistency_support_rank
    (D : conclusion_window6_local_support_ideal_four_rank_consistency_data) : ℕ :=
  D.conclusion_window6_local_support_ideal_four_rank_consistency_support.card

/-- The four ranks agree for every finite support subset of the audited window-`6` fibers. -/
def conclusion_window6_local_support_ideal_four_rank_consistency_statement
    (D : conclusion_window6_local_support_ideal_four_rank_consistency_data) : Prop :=
  (∀ y,
    y ∈ D.conclusion_window6_local_support_ideal_four_rank_consistency_support →
      conclusion_window6_local_support_ideal_four_rank_consistency_window6_size
        (D.conclusion_window6_local_support_ideal_four_rank_consistency_fiber_size y)) ∧
  conclusion_window6_local_support_ideal_four_rank_consistency_k0_rank D =
    D.conclusion_window6_local_support_ideal_four_rank_consistency_support.card ∧
  conclusion_window6_local_support_ideal_four_rank_consistency_center_dim D =
    D.conclusion_window6_local_support_ideal_four_rank_consistency_support.card ∧
  conclusion_window6_local_support_ideal_four_rank_consistency_abelian_rank D =
    D.conclusion_window6_local_support_ideal_four_rank_consistency_support.card ∧
  conclusion_window6_local_support_ideal_four_rank_consistency_support_rank D =
    D.conclusion_window6_local_support_ideal_four_rank_consistency_support.card

/-- Paper label: `thm:conclusion-window6-local-support-ideal-four-rank-consistency`. -/
theorem paper_conclusion_window6_local_support_ideal_four_rank_consistency
    (D : conclusion_window6_local_support_ideal_four_rank_consistency_data) :
    conclusion_window6_local_support_ideal_four_rank_consistency_statement D := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  intro y hy
  exact D.conclusion_window6_local_support_ideal_four_rank_consistency_fiber_size_mem y hy

end Omega.Conclusion
