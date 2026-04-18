import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Tactic
import Omega.Zeta.LocalizedIntegersCrossHomClassification

namespace Omega.Zeta

/-- Every localized cross-hom is determined by its image of `1`. -/
def localizedCrossHomDeterminedByOne (S T : FinitePrimeLocalization) : Prop :=
  ∀ φ ψ : LocalizedCrossHom S T,
    localizedCrossHomScalar φ = localizedCrossHomScalar ψ → φ.1 = ψ.1

/-- Endomorphisms of the local model are scalar multiplications by their value at `1`. -/
def localizedEndomorphismScalarDescription (S : FinitePrimeLocalization) : Prop :=
  ∀ φ : LocalizedCrossHom S S, ∀ z : LocalizedIntegerGroup S,
    φ.1 z = z * localizedCrossHomScalar φ

/-- Automorphisms of the local model are multiplication by a unit of `ℤ`, i.e. by `±1`. -/
def localizedAutomorphismUnitDescription (S : FinitePrimeLocalization) : Prop :=
  ∀ σ : LocalizedIntegerGroup S ≃+ LocalizedIntegerGroup S,
    ∃ u : ℤˣ, ∀ z : LocalizedIntegerGroup S, σ z = z * (u : ℤ)

/-- Complete local classification package for homomorphisms, endomorphisms, and automorphisms of
the simplified localized integer model. -/
def LocalizedHomAutCompleteClassification (S T : Omega.Zeta.FinitePrimeLocalization) : Prop :=
  LocalizedIntegersCrossHomClassification S T ∧
    localizedCrossHomDeterminedByOne S T ∧
    (∀ φ : LocalizedCrossHom S T, ∀ z : LocalizedIntegerGroup S,
      φ.1 z = z * localizedCrossHomScalar φ) ∧
    localizedEndomorphismScalarDescription S ∧
    localizedAutomorphismUnitDescription S

lemma localizedCrossHomDeterminedByOne_holds (S T : FinitePrimeLocalization) :
    localizedCrossHomDeterminedByOne S T := by
  intro φ ψ hφψ
  ext
  simpa [localizedCrossHomScalar] using hφψ

lemma localizedAutomorphism_eq_mul {S : FinitePrimeLocalization}
    (σ : LocalizedIntegerGroup S ≃+ LocalizedIntegerGroup S) (z : LocalizedIntegerGroup S) :
    σ z = z * σ 1 := by
  simpa [LocalizedIntegerGroup, zsmul_eq_mul] using σ.toAddMonoidHom.map_zsmul (1 : ℤ) z

lemma localizedAutomorphismUnitDescription_holds (S : FinitePrimeLocalization) :
    localizedAutomorphismUnitDescription S := by
  intro σ
  have hmul : σ 1 * σ.symm 1 = 1 := by
    calc
      σ 1 * σ.symm 1 = σ.symm (σ 1) := by
        symm
        exact localizedAutomorphism_eq_mul σ.symm (σ 1)
      _ = 1 := by simp
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hmul with hσ | hσ
  · refine ⟨1, ?_⟩
    intro z
    simpa [hσ] using localizedAutomorphism_eq_mul σ z
  · refine ⟨-1, ?_⟩
    intro z
    simpa [hσ] using localizedAutomorphism_eq_mul σ z

/-- The localized `Hom`-classification is scalar multiplication by the image of `1`, the
endomorphisms are the same specialization at `S = T`, and the automorphisms are exactly
multiplication by the unit group `ℤˣ = {±1}` in the local model.
    thm:xi-time-part69d-localized-hom-aut-complete-classification -/
theorem paper_xi_time_part69d_localized_hom_aut_complete_classification
    (S T : Omega.Zeta.FinitePrimeLocalization) : LocalizedHomAutCompleteClassification S T := by
  refine ⟨paper_xi_localized_integers_cross_hom_classification S T, ?_, ?_, ?_, ?_⟩
  · exact localizedCrossHomDeterminedByOne_holds S T
  · intro φ z
    exact localizedCrossHom_eq_mul φ z
  · intro φ z
    exact localizedCrossHom_eq_mul φ z
  · exact localizedAutomorphismUnitDescription_holds S

end Omega.Zeta
