import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import Omega.GroupUnification.BdryS3ToS2BreakingByGeoAxis

open Matrix

namespace Omega.GroupUnification

/-- The canonical `1 ⊔ 2` split singled out by fixing the boundary axis `i`. -/
def boundaryGeoAxisCanonicalSplit (i j : Fin 3) : Fin 2 :=
  if j = i then 0 else 1

/-- The grading operator recording the singleton axis versus its complementary two-plane. -/
def boundaryGeoAxisGrading (i : Fin 3) : Matrix (Fin 3) (Fin 3) ℚ :=
  Matrix.diagonal fun j => if j = i then (-1 : ℚ) else 1

/-- Block diagonal form relative to the `1 ⊕ 2` decomposition. -/
def boundaryGeoAxisBlockDiagonal (i : Fin 3) (A : Matrix (Fin 3) (Fin 3) ℚ) : Prop :=
  ∀ j : Fin 3, j ≠ i → A i j = 0 ∧ A j i = 0

/-- Paper-facing package for the fixed-axis `1 ⊔ 2` family split and the induced block-diagonal
constraint for operators commuting with the grading. -/
def bdryGeoAxisTwoPlusOneFamilySplittingStatement : Prop :=
  ∀ i : Fin 3,
    Nonempty ({σ : Equiv.Perm (Fin 3) // σ i = i} ≃ Equiv.Perm (Fin 2)) ∧
      boundaryGeoAxisCanonicalSplit i i = 0 ∧
      (∀ j : Fin 3, j ≠ i → boundaryGeoAxisCanonicalSplit i j = 1) ∧
      ∀ A : Matrix (Fin 3) (Fin 3) ℚ,
        A * boundaryGeoAxisGrading i = boundaryGeoAxisGrading i * A →
          boundaryGeoAxisBlockDiagonal i A

/-- Paper label: `cor:bdry-geo-axis-two-plus-one-family-splitting`. -/
def paper_bdry_geo_axis_two_plus_one_family_splitting : Prop :=
  bdryGeoAxisTwoPlusOneFamilySplittingStatement

private lemma boundaryGeoAxis_commuting_singleton_to_complement
    (i j : Fin 3) (hji : j ≠ i) (A : Matrix (Fin 3) (Fin 3) ℚ)
    (hcomm : A * boundaryGeoAxisGrading i = boundaryGeoAxisGrading i * A) :
    A i j = 0 := by
  have hentry := congrArg (fun M => M i j) hcomm
  simp [boundaryGeoAxisGrading, hji] at hentry
  linarith

private lemma boundaryGeoAxis_commuting_complement_to_singleton
    (i j : Fin 3) (hji : j ≠ i) (A : Matrix (Fin 3) (Fin 3) ℚ)
    (hcomm : A * boundaryGeoAxisGrading i = boundaryGeoAxisGrading i * A) :
    A j i = 0 := by
  have hentry := congrArg (fun M => M j i) hcomm
  simp [boundaryGeoAxisGrading, hji] at hentry
  linarith

theorem paper_bdry_geo_axis_two_plus_one_family_splitting_verified :
    paper_bdry_geo_axis_two_plus_one_family_splitting := by
  unfold paper_bdry_geo_axis_two_plus_one_family_splitting
    bdryGeoAxisTwoPlusOneFamilySplittingStatement
  intro i
  refine ⟨paper_bdry_s3_to_s2_breaking_by_geo_axis i, by simp [boundaryGeoAxisCanonicalSplit], ?_,
    ?_⟩
  · intro j hji
    simp [boundaryGeoAxisCanonicalSplit, hji]
  · intro A hcomm j hji
    exact ⟨boundaryGeoAxis_commuting_singleton_to_complement i j hji A hcomm,
      boundaryGeoAxis_commuting_complement_to_singleton i j hji A hcomm⟩

end Omega.GroupUnification
