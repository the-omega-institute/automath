import Mathlib.Data.Complex.Basic
import Omega.Conclusion.ArtinDeterminantMinimalVisibleQuotient
import Omega.Conclusion.FixedResolutionNontrivialCollisionMinimalCompleteStatistic

namespace Omega.Conclusion

open scoped BigOperators

/-- The fixed-resolution geometric side is the existing minimal-completeness package for the
nontrivial collision prefix. -/
def conclusion_fixedresolution_geometry_artin_orthogonal_splitting_geometric
    (r : ℕ) (delta mult : Fin r → ℕ) : Prop :=
  NontrivialCollisionPrefixMinimallyComplete (fun q => ∑ i, mult i * delta i ^ q)

/-- The Artin side is the determinant-visible quotient package attached to the active channels. -/
def conclusion_fixedresolution_geometry_artin_orthogonal_splitting_artin
    {G X : Type*} [Fintype G] [CommGroup G]
    (active : Finset X) (channel : X → G → Complex) (coeff : X → Complex)
    (determinantProfile : G → Complex)
    (channel_one : ∀ x, channel x 1 = 1)
    (channel_mul : ∀ x g h, channel x (g * h) = channel x g * channel x h)
    (determinant_expansion :
      ∀ g, determinantProfile g = Finset.sum active (fun x => channel x g * coeff x))
    (coeff_detects_kernel :
      ∀ k,
        (∀ c,
            Finset.sum active (fun x => channel x c * ((channel x k - 1) * coeff x)) = 0) →
          k ∈ primitiveMinimalCarrierKernel active channel channel_one channel_mul) : Prop :=
  let D : conclusion_artin_determinant_minimal_visible_quotient_data :=
    { G := G
      X := X
      instFintypeG := inferInstance
      instCommGroupG := inferInstance
      active := active
      channel := channel
      coeff := coeff
      determinantProfile := determinantProfile
      channel_one := channel_one
      channel_mul := channel_mul
      determinant_expansion := determinant_expansion
      coeff_detects_kernel := coeff_detects_kernel }
  D.minimal_quotient_preserves_determinant ∧ D.preservation_criterion ∧ D.unique_minimality

/-- The fixed-resolution geometric and Artin determinant packages split orthogonally into the
independent completeness and visible-quotient components. -/
def conclusion_fixedresolution_geometry_artin_orthogonal_splitting_statement
    {G X : Type*} [Fintype G] [CommGroup G]
    (r : ℕ) (delta mult : Fin r → ℕ)
    (active : Finset X) (channel : X → G → Complex) (coeff : X → Complex)
    (determinantProfile : G → Complex)
    (channel_one : ∀ x, channel x 1 = 1)
    (channel_mul : ∀ x g h, channel x (g * h) = channel x g * channel x h)
    (determinant_expansion :
      ∀ g, determinantProfile g = Finset.sum active (fun x => channel x g * coeff x))
    (coeff_detects_kernel :
      ∀ k,
        (∀ c,
            Finset.sum active (fun x => channel x c * ((channel x k - 1) * coeff x)) = 0) →
          k ∈ primitiveMinimalCarrierKernel active channel channel_one channel_mul) : Prop :=
  conclusion_fixedresolution_geometry_artin_orthogonal_splitting_geometric r delta mult ∧
    conclusion_fixedresolution_geometry_artin_orthogonal_splitting_artin active channel coeff
      determinantProfile channel_one channel_mul determinant_expansion coeff_detects_kernel

/-- Paper label: `thm:conclusion-fixedresolution-geometry-artin-orthogonal-splitting`. The
fixed-resolution geometric completeness package and the Artin determinant visible-quotient package
are available simultaneously, so the geometric side and the determinant-active nonabelian side
split as two orthogonal conclusion bullets. -/
theorem paper_conclusion_fixedresolution_geometry_artin_orthogonal_splitting
    {G X : Type*} [Fintype G] [CommGroup G]
    (r : ℕ) (delta mult : Fin r → ℕ) (hdelta : StrictMono delta) (hmult : ∀ i, 0 < mult i)
    (active : Finset X) (channel : X → G → Complex) (coeff : X → Complex)
    (determinantProfile : G → Complex)
    (channel_one : ∀ x, channel x 1 = 1)
    (channel_mul : ∀ x g h, channel x (g * h) = channel x g * channel x h)
    (determinant_expansion :
      ∀ g, determinantProfile g = Finset.sum active (fun x => channel x g * coeff x))
    (coeff_detects_kernel :
      ∀ k,
        (∀ c,
            Finset.sum active (fun x => channel x c * ((channel x k - 1) * coeff x)) = 0) →
          k ∈ primitiveMinimalCarrierKernel active channel channel_one channel_mul) :
    conclusion_fixedresolution_geometry_artin_orthogonal_splitting_statement r delta mult active
      channel coeff determinantProfile channel_one channel_mul determinant_expansion
      coeff_detects_kernel := by
  refine ⟨?_, ?_⟩
  · exact
      paper_conclusion_fixedresolution_nontrivial_collision_minimal_complete_statistic r delta mult
        hdelta hmult
  · let D : conclusion_artin_determinant_minimal_visible_quotient_data :=
      { G := G
        X := X
        instFintypeG := inferInstance
        instCommGroupG := inferInstance
        active := active
        channel := channel
        coeff := coeff
        determinantProfile := determinantProfile
        channel_one := channel_one
        channel_mul := channel_mul
        determinant_expansion := determinant_expansion
        coeff_detects_kernel := coeff_detects_kernel }
    simpa [conclusion_fixedresolution_geometry_artin_orthogonal_splitting_artin] using
      paper_conclusion_artin_determinant_minimal_visible_quotient D

end Omega.Conclusion
