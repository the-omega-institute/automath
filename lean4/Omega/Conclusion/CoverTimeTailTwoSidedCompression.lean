import Mathlib.Tactic
import Omega.Conclusion.MissingTypeFirstSecondMoments

namespace Omega.Conclusion

/-- Deterministic cover-time tail event in the without-replacement model. -/
def conclusion_cover_time_tail_two_sided_compression_tau_exceeds (N t : ℕ) : Prop :=
  t < N

/-- Deterministic missing-type count after `t` draws. -/
def conclusion_cover_time_tail_two_sided_compression_missing_count (N t : ℕ) : ℕ :=
  N - t

/-- Tail probability of the deterministic cover-time model. -/
def conclusion_cover_time_tail_two_sided_compression_tail_probability (N t : ℕ) : ℚ :=
  if t < N then 1 else 0

theorem conclusion_cover_time_tail_two_sided_compression_tau_iff_missing_positive
    (N t : ℕ) :
    conclusion_cover_time_tail_two_sided_compression_tau_exceeds N t ↔
      0 < conclusion_cover_time_tail_two_sided_compression_missing_count N t := by
  unfold conclusion_cover_time_tail_two_sided_compression_tau_exceeds
    conclusion_cover_time_tail_two_sided_compression_missing_count
  constructor
  · intro ht
    exact Nat.sub_pos_of_lt ht
  · intro hMissing
    exact Nat.lt_of_sub_pos hMissing

/-- Concrete two-sided compression statement: the deterministic cover-time tail is sandwiched
between the Paley--Zygmund lower bound and the first-moment upper bound derived from the
missing-type count. -/
def conclusion_cover_time_tail_two_sided_compression_statement : Prop :=
  ∀ N t : ℕ, t ≤ N → 2 ≤ N →
    (conclusion_cover_time_tail_two_sided_compression_tau_exceeds N t ↔
      0 < conclusion_cover_time_tail_two_sided_compression_missing_count N t) ∧
    let p := conclusion_cover_time_tail_two_sided_compression_tail_probability N t
    let μ := conclusion_missing_type_first_second_moments_missing_count_mean N t
    let σ2 := conclusion_missing_type_first_second_moments_missing_count_variance N t
    μ * μ / (μ * μ + σ2) ≤ p ∧ p ≤ μ

/-- Paper label wrapper for the deterministic two-sided cover-time tail compression.
    cor:conclusion-cover-time-tail-two-sided-compression -/
def paper_conclusion_cover_time_tail_two_sided_compression : Prop :=
  conclusion_cover_time_tail_two_sided_compression_statement

end Omega.Conclusion
