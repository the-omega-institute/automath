import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete data for the Prym Neron-Severi rank audit. The natural-number fields record the
isogeny-to-`R^2` input, the three independent algebraic classes, the no-CM endomorphism reduction,
and the Rosati fixed-space dimension. -/
structure conclusion_prym_ns_rank_lower_and_nocm_exact_data where
  conclusion_prym_ns_rank_lower_and_nocm_exact_prym_ns_rank : ℕ
  conclusion_prym_ns_rank_lower_and_nocm_exact_cycle_class_count : ℕ
  conclusion_prym_ns_rank_lower_and_nocm_exact_endomorphism_dim_under_no_cm : ℕ
  conclusion_prym_ns_rank_lower_and_nocm_exact_rosati_fixed_dim : ℕ
  conclusion_prym_ns_rank_lower_and_nocm_exact_isogeny_factor_count : ℕ
  conclusion_prym_ns_rank_lower_and_nocm_exact_isogeny_factor_count_eq_two :
    conclusion_prym_ns_rank_lower_and_nocm_exact_isogeny_factor_count = 2
  conclusion_prym_ns_rank_lower_and_nocm_exact_cycle_class_count_eq_three :
    conclusion_prym_ns_rank_lower_and_nocm_exact_cycle_class_count = 3
  conclusion_prym_ns_rank_lower_and_nocm_exact_cycle_classes_independent :
    conclusion_prym_ns_rank_lower_and_nocm_exact_cycle_class_count ≤
      conclusion_prym_ns_rank_lower_and_nocm_exact_prym_ns_rank
  conclusion_prym_ns_rank_lower_and_nocm_exact_no_cm_endomorphism_dim :
    conclusion_prym_ns_rank_lower_and_nocm_exact_endomorphism_dim_under_no_cm = 4 →
      conclusion_prym_ns_rank_lower_and_nocm_exact_prym_ns_rank = 3
  conclusion_prym_ns_rank_lower_and_nocm_exact_no_cm_rosati_dim :
    conclusion_prym_ns_rank_lower_and_nocm_exact_endomorphism_dim_under_no_cm = 4 →
      conclusion_prym_ns_rank_lower_and_nocm_exact_rosati_fixed_dim = 3

namespace conclusion_prym_ns_rank_lower_and_nocm_exact_data

/-- The lower bound supplied by the two coordinate classes and the diagonal class. -/
def conclusion_prym_ns_rank_lower_bound
    (D : conclusion_prym_ns_rank_lower_and_nocm_exact_data) : Prop :=
  3 ≤ D.conclusion_prym_ns_rank_lower_and_nocm_exact_prym_ns_rank

/-- The no-CM input reduces the endomorphism algebra to the `M₂(ℚ)` model. -/
def conclusion_prym_ns_rank_lower_and_nocm_exact_no_cm
    (D : conclusion_prym_ns_rank_lower_and_nocm_exact_data) : Prop :=
  D.conclusion_prym_ns_rank_lower_and_nocm_exact_endomorphism_dim_under_no_cm = 4

/-- Exact Neron-Severi rank in the no-CM case. -/
def conclusion_prym_ns_rank_exact
    (D : conclusion_prym_ns_rank_lower_and_nocm_exact_data) : Prop :=
  D.conclusion_prym_ns_rank_lower_and_nocm_exact_prym_ns_rank = 3

/-- Rosati fixed-space dimension in the no-CM case. -/
def conclusion_prym_rosati_fixed_dim_eq_three
    (D : conclusion_prym_ns_rank_lower_and_nocm_exact_data) : Prop :=
  D.conclusion_prym_ns_rank_lower_and_nocm_exact_rosati_fixed_dim = 3

end conclusion_prym_ns_rank_lower_and_nocm_exact_data

open conclusion_prym_ns_rank_lower_and_nocm_exact_data

/-- Paper label: `prop:conclusion-prym-ns-rank-lower-and-nocm-exact`. -/
theorem paper_conclusion_prym_ns_rank_lower_and_nocm_exact
    (D : conclusion_prym_ns_rank_lower_and_nocm_exact_data) :
    D.conclusion_prym_ns_rank_lower_bound ∧
      (D.conclusion_prym_ns_rank_lower_and_nocm_exact_no_cm →
        D.conclusion_prym_ns_rank_exact ∧ D.conclusion_prym_rosati_fixed_dim_eq_three) := by
  refine ⟨?_, ?_⟩
  · unfold conclusion_prym_ns_rank_lower_bound
    rw [← D.conclusion_prym_ns_rank_lower_and_nocm_exact_cycle_class_count_eq_three]
    exact D.conclusion_prym_ns_rank_lower_and_nocm_exact_cycle_classes_independent
  · intro hNoCM
    exact
      ⟨D.conclusion_prym_ns_rank_lower_and_nocm_exact_no_cm_endomorphism_dim hNoCM,
        D.conclusion_prym_ns_rank_lower_and_nocm_exact_no_cm_rosati_dim hNoCM⟩

end Omega.Conclusion
