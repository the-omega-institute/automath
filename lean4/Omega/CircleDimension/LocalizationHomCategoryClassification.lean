import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic
import Omega.CircleDimension.LocalizedGsEmbeddingOrder

namespace Omega.CircleDimension

open LocalizedGsEmbeddingOrderData

/-- Scalar models for additive homomorphisms `G_S → G_T`: multiplication by a rational whose
action preserves the localized subgroup `G_S ⊆ ℚ`. -/
def localizedHomScalar (S T : Finset ℕ) :=
  { q : ℚ // ∀ r : ℚ, inLocalizedGs S r → inLocalizedGs T (q * r) }

/-- Scalars whose multiplication map is an automorphism of `G_S`. -/
def localizedUnitScalar (S : Finset ℕ) :=
  { q : ℚ // q ≠ 0 ∧ inLocalizedGs S q ∧ inLocalizedGs S q⁻¹ }

/-- Scalar witnesses for isomorphisms between localizations. -/
def localizedIsoScalar (S T : Finset ℕ) :=
  { q : ℚ // q ≠ 0 ∧
      (∀ r : ℚ, inLocalizedGs S r → inLocalizedGs T (q * r)) ∧
      (∀ r : ℚ, inLocalizedGs T r → inLocalizedGs S (q⁻¹ * r)) }

/-- Swap source and target supports. -/
private def localizedGsEmbeddingOrderSwap
    (D : LocalizedGsEmbeddingOrderData) : LocalizedGsEmbeddingOrderData where
  S := D.T
  T := D.S
  S_primes := D.T_primes
  T_primes := D.S_primes

private lemma subset_inLocalizedGs {S T : Finset ℕ} (hST : S ⊆ T) {q : ℚ}
    (hq : inLocalizedGs S q) : inLocalizedGs T q := by
  intro p hp hpden
  exact hST (hq p hp hpden)

private lemma inLocalizedGs_mul {S : Finset ℕ} {q r : ℚ} (hq : inLocalizedGs S q)
    (hr : inLocalizedGs S r) : inLocalizedGs S (q * r) := by
  intro p hp hpden
  have hprod : p ∣ q.den * r.den := dvd_trans hpden (Rat.mul_den_dvd q r)
  rcases (Nat.Prime.dvd_mul hp).mp hprod with hqden | hrden
  · exact hq p hp hqden
  · exact hr p hp hrden

private def localizedHomScalarEquivTarget {S T : Finset ℕ} (hST : S ⊆ T) :
    localizedHomScalar S T ≃ { q : ℚ // inLocalizedGs T q } where
  toFun f := ⟨f.1, by simpa using f.2 1 (one_mem S)⟩
  invFun q := ⟨q.1, fun r hr => inLocalizedGs_mul q.2 (subset_inLocalizedGs hST hr)⟩
  left_inv f := by
    apply Subtype.ext
    rfl
  right_inv q := by
    apply Subtype.ext
    rfl

private lemma localizedHomScalar_zero_of_not_subset (D : LocalizedGsEmbeddingOrderData)
    (hST : ¬ D.S ⊆ D.T) (f : localizedHomScalar D.S D.T) : f.1 = 0 := by
  by_contra hf0
  have hEmb : localizedEmbedding D.S D.T := ⟨f.1, hf0, f.2⟩
  exact hST (D.subset_of_localizedEmbedding hEmb)

private lemma localizedHomScalar_subsingleton_of_not_subset (D : LocalizedGsEmbeddingOrderData)
    (hST : ¬ D.S ⊆ D.T) : Subsingleton (localizedHomScalar D.S D.T) := by
  refine ⟨?_⟩
  intro f g
  apply Subtype.ext
  exact (localizedHomScalar_zero_of_not_subset D hST f).trans
    (localizedHomScalar_zero_of_not_subset D hST g).symm

private def localizedIsoScalarEquivUnit (S : Finset ℕ) :
    localizedIsoScalar S S ≃ localizedUnitScalar S where
  toFun q :=
    ⟨q.1, q.2.1, by simpa using q.2.2.1 1 (one_mem S), by simpa using q.2.2.2 1 (one_mem S)⟩
  invFun q :=
    ⟨q.1, q.2.1,
      (fun r hr => inLocalizedGs_mul q.2.2.1 hr),
      fun r hr => inLocalizedGs_mul q.2.2.2 hr⟩
  left_inv q := by
    apply Subtype.ext
    rfl
  right_inv q := by
    apply Subtype.ext
    rfl

private lemma localizedIsoScalar_nonempty_iff_eq (D : LocalizedGsEmbeddingOrderData) :
    Nonempty (localizedIsoScalar D.S D.T) ↔ D.S = D.T := by
  constructor
  · rintro ⟨q⟩
    have hST : D.S ⊆ D.T := D.subset_of_localizedEmbedding ⟨q.1, q.2.1, q.2.2.1⟩
    have hTS : D.T ⊆ D.S :=
      (localizedGsEmbeddingOrderSwap D).subset_of_localizedEmbedding
        ⟨q.1⁻¹, inv_ne_zero q.2.1, q.2.2.2⟩
    exact Finset.Subset.antisymm hST hTS
  · intro hST
    refine ⟨⟨1, one_ne_zero, ?_, ?_⟩⟩
    · intro r hr
      simpa [hST] using hr
    · intro r hr
      simpa [hST] using hr

/-- Every additive morphism `G_S → G_T` is determined by the image of `1`, so when `S ⊆ T` the
whole Hom-set is identified with `G_T`, while for `S ⊈ T` only the zero scalar remains.
Specializing to `S = T` gives the endomorphism classification; restricting to invertible scalars
gives the automorphism classification; and isomorphisms occur exactly when `S = T`.
    thm:xi-cdim-localization-hom-category-classification -/
theorem paper_xi_cdim_localization_hom_category_classification
    (D : LocalizedGsEmbeddingOrderData) :
    (D.S ⊆ D.T → Nonempty (localizedHomScalar D.S D.T ≃ { q : ℚ // inLocalizedGs D.T q })) ∧
      (¬ D.S ⊆ D.T → Subsingleton (localizedHomScalar D.S D.T)) ∧
      Nonempty (localizedHomScalar D.S D.S ≃ { q : ℚ // inLocalizedGs D.S q }) ∧
      Nonempty (localizedIsoScalar D.S D.S ≃ localizedUnitScalar D.S) ∧
      (Nonempty (localizedIsoScalar D.S D.T) ↔ D.S = D.T) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hST
    exact ⟨localizedHomScalarEquivTarget hST⟩
  · intro hST
    exact localizedHomScalar_subsingleton_of_not_subset D hST
  · exact ⟨localizedHomScalarEquivTarget (by intro p hp; exact hp)⟩
  · exact ⟨localizedIsoScalarEquivUnit D.S⟩
  · exact localizedIsoScalar_nonempty_iff_eq D

end Omega.CircleDimension
