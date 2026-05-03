import Omega.Conclusion.BoundaryGodelSeparatedUnionAdhesionMaxlaw

namespace Omega.Conclusion

/-- Concrete storage/adhesion exponent data for a positive-distance separated union. -/
structure conclusion_boundary_godel_separated_union_storage_maxlaw_data where
  conclusion_boundary_godel_separated_union_storage_maxlaw_storageA : ℝ
  conclusion_boundary_godel_separated_union_storage_maxlaw_storageB : ℝ
  conclusion_boundary_godel_separated_union_storage_maxlaw_storageUnion : ℝ
  conclusion_boundary_godel_separated_union_storage_maxlaw_adhesionA : ℝ
  conclusion_boundary_godel_separated_union_storage_maxlaw_adhesionB : ℝ
  conclusion_boundary_godel_separated_union_storage_maxlaw_adhesionUnion : ℝ
  conclusion_boundary_godel_separated_union_storage_maxlaw_storageA_eq_adhesionA :
    conclusion_boundary_godel_separated_union_storage_maxlaw_storageA =
      conclusion_boundary_godel_separated_union_storage_maxlaw_adhesionA
  conclusion_boundary_godel_separated_union_storage_maxlaw_storageB_eq_adhesionB :
    conclusion_boundary_godel_separated_union_storage_maxlaw_storageB =
      conclusion_boundary_godel_separated_union_storage_maxlaw_adhesionB
  conclusion_boundary_godel_separated_union_storage_maxlaw_storageUnion_eq_adhesionUnion :
    conclusion_boundary_godel_separated_union_storage_maxlaw_storageUnion =
      conclusion_boundary_godel_separated_union_storage_maxlaw_adhesionUnion
  conclusion_boundary_godel_separated_union_storage_maxlaw_adhesionUnion_eq_max :
    conclusion_boundary_godel_separated_union_storage_maxlaw_adhesionUnion =
      max conclusion_boundary_godel_separated_union_storage_maxlaw_adhesionA
        conclusion_boundary_godel_separated_union_storage_maxlaw_adhesionB

namespace conclusion_boundary_godel_separated_union_storage_maxlaw_data

/-- The storage exponent of a separated union is the maximum storage exponent of the components. -/
def storage_exponent_max_law
    (D : conclusion_boundary_godel_separated_union_storage_maxlaw_data) : Prop :=
  D.conclusion_boundary_godel_separated_union_storage_maxlaw_storageUnion =
    max D.conclusion_boundary_godel_separated_union_storage_maxlaw_storageA
      D.conclusion_boundary_godel_separated_union_storage_maxlaw_storageB

lemma conclusion_boundary_godel_separated_union_storage_maxlaw_storage_exponent
    (D : conclusion_boundary_godel_separated_union_storage_maxlaw_data) :
    D.storage_exponent_max_law := by
  calc
    D.conclusion_boundary_godel_separated_union_storage_maxlaw_storageUnion =
        D.conclusion_boundary_godel_separated_union_storage_maxlaw_adhesionUnion :=
      D.conclusion_boundary_godel_separated_union_storage_maxlaw_storageUnion_eq_adhesionUnion
    _ = max D.conclusion_boundary_godel_separated_union_storage_maxlaw_adhesionA
          D.conclusion_boundary_godel_separated_union_storage_maxlaw_adhesionB :=
      D.conclusion_boundary_godel_separated_union_storage_maxlaw_adhesionUnion_eq_max
    _ = max D.conclusion_boundary_godel_separated_union_storage_maxlaw_storageA
          D.conclusion_boundary_godel_separated_union_storage_maxlaw_storageB := by
      rw [← D.conclusion_boundary_godel_separated_union_storage_maxlaw_storageA_eq_adhesionA,
        ← D.conclusion_boundary_godel_separated_union_storage_maxlaw_storageB_eq_adhesionB]

end conclusion_boundary_godel_separated_union_storage_maxlaw_data

/-- Paper label: `cor:conclusion-boundary-godel-separated-union-storage-maxlaw`. -/
theorem paper_conclusion_boundary_godel_separated_union_storage_maxlaw
    (D : conclusion_boundary_godel_separated_union_storage_maxlaw_data) :
    D.storage_exponent_max_law := by
  exact D.conclusion_boundary_godel_separated_union_storage_maxlaw_storage_exponent

end Omega.Conclusion
