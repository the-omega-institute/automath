import Mathlib.Tactic

namespace Omega.Conclusion

/-- The four normalized offline-failure tags used by the quadriga certificate. -/
inductive conclusion_offline_failure_semantics_minimal_complete_quadriga_failure_tag where
  | conclusion_offline_failure_semantics_minimal_complete_quadriga_semantic
  | conclusion_offline_failure_semantics_minimal_complete_quadriga_protocol
  | conclusion_offline_failure_semantics_minimal_complete_quadriga_collision
  | conclusion_offline_failure_semantics_minimal_complete_quadriga_dimension
  deriving DecidableEq, Fintype

/-- Normalized offline-failure data: tag, location, lower-bound counter, and auxiliary code. -/
structure conclusion_offline_failure_semantics_minimal_complete_quadriga_normalized_failure where
  conclusion_offline_failure_semantics_minimal_complete_quadriga_tag :
    conclusion_offline_failure_semantics_minimal_complete_quadriga_failure_tag
  conclusion_offline_failure_semantics_minimal_complete_quadriga_location : ℕ
  conclusion_offline_failure_semantics_minimal_complete_quadriga_lowerBound : ℕ
  conclusion_offline_failure_semantics_minimal_complete_quadriga_auxiliary : ℕ

/-- A tag family covers all normalized failures when every failure tag lies in it. -/
def conclusion_offline_failure_semantics_minimal_complete_quadriga_covers
    (S :
      Finset conclusion_offline_failure_semantics_minimal_complete_quadriga_failure_tag) :
    Prop :=
  ∀ W : conclusion_offline_failure_semantics_minimal_complete_quadriga_normalized_failure,
    W.conclusion_offline_failure_semantics_minimal_complete_quadriga_tag ∈ S

/-- A canonical normalized witness for a requested tag. -/
def conclusion_offline_failure_semantics_minimal_complete_quadriga_witness
    (tag : conclusion_offline_failure_semantics_minimal_complete_quadriga_failure_tag) :
    conclusion_offline_failure_semantics_minimal_complete_quadriga_normalized_failure where
  conclusion_offline_failure_semantics_minimal_complete_quadriga_tag := tag
  conclusion_offline_failure_semantics_minimal_complete_quadriga_location := 0
  conclusion_offline_failure_semantics_minimal_complete_quadriga_lowerBound := 0
  conclusion_offline_failure_semantics_minimal_complete_quadriga_auxiliary := 0

/-- Completeness plus one-witness minimality of the four-tag offline-failure semantics. -/
def conclusion_offline_failure_semantics_minimal_complete_quadriga_statement : Prop :=
  (∀ W : conclusion_offline_failure_semantics_minimal_complete_quadriga_normalized_failure,
    W.conclusion_offline_failure_semantics_minimal_complete_quadriga_tag =
        conclusion_offline_failure_semantics_minimal_complete_quadriga_failure_tag.conclusion_offline_failure_semantics_minimal_complete_quadriga_semantic ∨
      W.conclusion_offline_failure_semantics_minimal_complete_quadriga_tag =
        conclusion_offline_failure_semantics_minimal_complete_quadriga_failure_tag.conclusion_offline_failure_semantics_minimal_complete_quadriga_protocol ∨
      W.conclusion_offline_failure_semantics_minimal_complete_quadriga_tag =
        conclusion_offline_failure_semantics_minimal_complete_quadriga_failure_tag.conclusion_offline_failure_semantics_minimal_complete_quadriga_collision ∨
      W.conclusion_offline_failure_semantics_minimal_complete_quadriga_tag =
        conclusion_offline_failure_semantics_minimal_complete_quadriga_failure_tag.conclusion_offline_failure_semantics_minimal_complete_quadriga_dimension) ∧
    conclusion_offline_failure_semantics_minimal_complete_quadriga_covers Finset.univ ∧
      ∀ tag : conclusion_offline_failure_semantics_minimal_complete_quadriga_failure_tag,
        ¬ conclusion_offline_failure_semantics_minimal_complete_quadriga_covers
          (Finset.univ.erase tag)

/-- Paper label:
`thm:conclusion-offline-failure-semantics-minimal-complete-quadriga`. -/
theorem paper_conclusion_offline_failure_semantics_minimal_complete_quadriga :
    conclusion_offline_failure_semantics_minimal_complete_quadriga_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro W
    cases W.conclusion_offline_failure_semantics_minimal_complete_quadriga_tag <;> simp
  · intro W
    simp
  · intro tag hcover
    have hmem :=
      hcover
        (conclusion_offline_failure_semantics_minimal_complete_quadriga_witness tag)
    simp [conclusion_offline_failure_semantics_minimal_complete_quadriga_witness] at hmem

end Omega.Conclusion
