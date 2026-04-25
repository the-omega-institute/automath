import Mathlib.Tactic

namespace Omega.Conclusion

theorem paper_conclusion_boundary_godel_separated_union_adhesion_maxlaw
    (boundaryA boundaryB boundaryUnion adhesionA adhesionB adhesionUnion : Real)
    (hBoundary : boundaryUnion = max boundaryA boundaryB)
    (hA : boundaryA = adhesionA) (hB : boundaryB = adhesionB)
    (hUnion : boundaryUnion = adhesionUnion) :
    adhesionUnion = max adhesionA adhesionB := by
  calc
    adhesionUnion = boundaryUnion := hUnion.symm
    _ = max boundaryA boundaryB := hBoundary
    _ = max adhesionA adhesionB := by rw [hA, hB]

end Omega.Conclusion
