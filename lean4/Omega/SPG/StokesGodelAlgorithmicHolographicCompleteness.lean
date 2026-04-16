import Omega.SPG.BoundaryGodelizationHolographicDictionary
import Omega.SPG.DyadicCubicalBoundaryInjective

namespace Omega.SPG

/-- Chapter-local data for the Stokes--Gödel algorithmic holographic completeness wrapper.
The structure records a top-dimensional boundary map, a computable Gödel coding of boundary data,
and a decoder on the image. The output clauses package constant-overhead complexity preservation,
recoverability from the code, and a code-computable volume functional. -/
structure StokesGodelAlgorithmicHolographicCompletenessData where
  Bulk : Type
  Boundary : Type
  Code : Type
  bulkAddGroup : AddGroup Bulk
  boundaryAddGroup : AddGroup Boundary
  toBoundary : Bulk → Boundary
  toCode : Boundary → Code
  boundary_sub : ∀ u v, toBoundary (u - v) = toBoundary u - toBoundary v
  boundary_kernel : ∀ u, toBoundary u = 0 → u = 0
  code_injective : Function.Injective toCode
  decode : Set.range (toCode ∘ toBoundary) → Bulk
  decode_spec : ∀ u, decode ⟨(toCode ∘ toBoundary) u, ⟨u, rfl⟩⟩ = u
  complexityPreserved : Prop
  bulkRecoverableFromCode : Prop
  volumeComputableFromCode : Prop
  complexity_of_injective_dictionary :
    Function.Injective (toCode ∘ toBoundary) → complexityPreserved
  recoverability_of_decoder :
    (∀ u, decode ⟨(toCode ∘ toBoundary) u, ⟨u, rfl⟩⟩ = u) → bulkRecoverableFromCode
  volume_of_decoder : (Set.range (toCode ∘ toBoundary) → Bulk) → volumeComputableFromCode

/-- If the top-dimensional dyadic boundary map is injective and the boundary Gödelization is
injective, then the composite Stokes--Gödel code is an injective dictionary. A decoder on the
image therefore yields constant-overhead recoverability and a code-computable volume readout.
    thm:spg-stokes-godel-algorithmic-holographic-completeness -/
theorem paper_spg_stokes_godel_algorithmic_holographic_completeness
    (D : StokesGodelAlgorithmicHolographicCompletenessData) :
    D.complexityPreserved ∧ D.bulkRecoverableFromCode ∧ D.volumeComputableFromCode := by
  let _ : AddGroup D.Bulk := D.bulkAddGroup
  let _ : AddGroup D.Boundary := D.boundaryAddGroup
  have hBoundary : Function.Injective D.toBoundary :=
    paper_spg_dyadic_cubical_boundary_injective
      D.toBoundary D.boundary_sub D.boundary_kernel
  have hDictionary : Function.Injective (D.toCode ∘ D.toBoundary) :=
    paper_spg_boundary_godelization_holographic_dictionary
      D.toBoundary D.toCode hBoundary D.code_injective
  exact ⟨D.complexity_of_injective_dictionary hDictionary,
    D.recoverability_of_decoder D.decode_spec,
    D.volume_of_decoder D.decode⟩

end Omega.SPG
