import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete one-parameter package for
`thm:conclusion-fiber-permutation-logvolume-constant-error-sharpp-hard`.  The
single-collapse reduction supplies an even collapsed fiber size, an approximation to
the encoded log-volume, and the relation between that even size and the SAT count. -/
structure conclusion_fiber_permutation_logvolume_constant_error_sharpp_hard_data where
  conclusion_fiber_permutation_logvolume_constant_error_sharpp_hard_collapsedSize : ℕ
  conclusion_fiber_permutation_logvolume_constant_error_sharpp_hard_satCount : ℕ
  conclusion_fiber_permutation_logvolume_constant_error_sharpp_hard_approximation : ℕ
  conclusion_fiber_permutation_logvolume_constant_error_sharpp_hard_collapsedSize_even :
    Even conclusion_fiber_permutation_logvolume_constant_error_sharpp_hard_collapsedSize
  conclusion_fiber_permutation_logvolume_constant_error_sharpp_hard_collapse_relation :
    conclusion_fiber_permutation_logvolume_constant_error_sharpp_hard_collapsedSize =
      2 * conclusion_fiber_permutation_logvolume_constant_error_sharpp_hard_satCount
  conclusion_fiber_permutation_logvolume_constant_error_sharpp_hard_approximation_exact :
    conclusion_fiber_permutation_logvolume_constant_error_sharpp_hard_approximation =
      conclusion_fiber_permutation_logvolume_constant_error_sharpp_hard_collapsedSize / 2

namespace conclusion_fiber_permutation_logvolume_constant_error_sharpp_hard_data

/-- The discrete log-volume code used on the even single-collapse fiber sizes. -/
def conclusion_fiber_permutation_logvolume_constant_error_sharpp_hard_logvolume
    (s : ℕ) : ℕ :=
  s / 2

/-- Adjacent even collapsed fiber sizes are separated by one unit in the log-volume code. -/
def conclusion_fiber_permutation_logvolume_constant_error_sharpp_hard_even_gap : Prop :=
  ∀ t : ℕ,
    Even t →
      conclusion_fiber_permutation_logvolume_constant_error_sharpp_hard_logvolume (t + 2) =
        conclusion_fiber_permutation_logvolume_constant_error_sharpp_hard_logvolume t + 1

/-- The constant-error approximation recovers the collapsed even size and hence the SAT count. -/
def conclusion_fiber_permutation_logvolume_constant_error_sharpp_hard_recovery
    (D : conclusion_fiber_permutation_logvolume_constant_error_sharpp_hard_data) : Prop :=
  ∃ recovered,
    recovered = D.conclusion_fiber_permutation_logvolume_constant_error_sharpp_hard_satCount ∧
      D.conclusion_fiber_permutation_logvolume_constant_error_sharpp_hard_collapsedSize =
        2 * recovered ∧
      D.conclusion_fiber_permutation_logvolume_constant_error_sharpp_hard_approximation =
        conclusion_fiber_permutation_logvolume_constant_error_sharpp_hard_logvolume
          (2 * recovered)

/-- Concrete statement assembled for
`thm:conclusion-fiber-permutation-logvolume-constant-error-sharpp-hard`. -/
def statement
    (D : conclusion_fiber_permutation_logvolume_constant_error_sharpp_hard_data) : Prop :=
  conclusion_fiber_permutation_logvolume_constant_error_sharpp_hard_even_gap ∧
    D.conclusion_fiber_permutation_logvolume_constant_error_sharpp_hard_recovery

end conclusion_fiber_permutation_logvolume_constant_error_sharpp_hard_data

open conclusion_fiber_permutation_logvolume_constant_error_sharpp_hard_data

/-- Paper label:
`thm:conclusion-fiber-permutation-logvolume-constant-error-sharpp-hard`. -/
theorem paper_conclusion_fiber_permutation_logvolume_constant_error_sharpp_hard
    (D : conclusion_fiber_permutation_logvolume_constant_error_sharpp_hard_data) :
    D.statement := by
  constructor
  · intro t ht
    rcases ht with ⟨k, rfl⟩
    unfold conclusion_fiber_permutation_logvolume_constant_error_sharpp_hard_logvolume
    omega
  · refine
      ⟨D.conclusion_fiber_permutation_logvolume_constant_error_sharpp_hard_satCount, rfl,
        D.conclusion_fiber_permutation_logvolume_constant_error_sharpp_hard_collapse_relation,
        ?_⟩
    rw [← D.conclusion_fiber_permutation_logvolume_constant_error_sharpp_hard_collapse_relation]
    simpa [conclusion_fiber_permutation_logvolume_constant_error_sharpp_hard_logvolume] using
      D.conclusion_fiber_permutation_logvolume_constant_error_sharpp_hard_approximation_exact

end Omega.Conclusion
