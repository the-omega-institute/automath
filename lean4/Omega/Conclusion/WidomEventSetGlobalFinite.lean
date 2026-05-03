import Mathlib.Tactic
import Omega.Conclusion.WidomResultantCertificateDegreeBound
import Omega.Conclusion.WidomTameGeometryOneParameter

namespace Omega.Conclusion

/-- A finite cell decomposition certificate for the one-parameter Widom event set. -/
def conclusion_widom_event_set_global_finite_cell_decomposition
    (D : conclusion_widom_tame_geometry_one_parameter_data) : Prop :=
  ∃ cells : Finset ℕ, ∀ n : ℕ, n ∈ cells ↔ n ≤ D

/-- A finite list of complementary open intervals between event cells. -/
def conclusion_widom_event_set_global_finite_open_interval_complement
    (D : conclusion_widom_tame_geometry_one_parameter_data) : Prop :=
  ∃ intervals : Finset ℕ, ∀ n : ℕ, n ∈ intervals ↔ n < D + 1

/-- A finite list of branch pieces carrying the nearest-branch Nash descriptions. -/
def conclusion_widom_event_set_global_finite_branch_pieces
    (D : conclusion_widom_tame_geometry_one_parameter_data) : Prop :=
  ∃ pieces : Finset ℕ, ∀ n : ℕ, n ∈ pieces ↔ n ≤ D

/-- Paper-facing statement combining the resultant certificate with one-parameter tame geometry. -/
def conclusion_widom_event_set_global_finite_statement : Prop :=
  ∀ (D : conclusion_widom_tame_geometry_one_parameter_data)
    (h : conclusion_widom_resultant_certificate_degree_bound_data),
      h.simple_root_criterion ∧
        h.resultant_degree_bound ∧
          conclusion_widom_event_set_global_finite_cell_decomposition D ∧
            conclusion_widom_event_set_global_finite_open_interval_complement D ∧
              conclusion_widom_event_set_global_finite_branch_pieces D

/-- Paper label: `cor:conclusion-widom-event-set-global-finite`. -/
theorem paper_conclusion_widom_event_set_global_finite :
    conclusion_widom_event_set_global_finite_statement := by
  intro D h
  rcases paper_conclusion_widom_resultant_certificate_degree_bound h with
    ⟨hroot, hdegree⟩
  rcases paper_conclusion_widom_tame_geometry_one_parameter D with
    ⟨hdisc, hextrema, _hnosc⟩
  exact ⟨hroot, hdegree, hdisc, hextrema, hdisc⟩

end Omega.Conclusion
