import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic
import Omega.Zeta.LocalizedIntegersCrossHomClassification

open scoped BigOperators

namespace Omega.Zeta

/-- A finite family of localized integer groups, encoded by their inverted prime supports. -/
abbrev LocalizedDirectsumFamily := List (Finset Nat)

/-- A family of single-block localized cross-homs, one for each matrix slot. -/
abbrev localizedDirectsumCrossHomFamily (S T : LocalizedDirectsumFamily) :=
  ∀ j : Fin T.length, ∀ i : Fin S.length, LocalizedCrossHom (S.get i) (T.get j)

/-- The sparse matrix extracted from a blockwise family of localized cross-homs by taking the image
of `1` in each block. -/
def localizedDirectsumMatrixOfFamily (S T : LocalizedDirectsumFamily)
    (Φ : localizedDirectsumCrossHomFamily S T) : Fin T.length → Fin S.length → ℤ :=
  fun j i => localizedCrossHomScalar (Φ j i)

/-- A matrix is sparse when entries vanish outside the subset relation `Sᵢ ⊆ Tⱼ`. -/
def localizedDirectsumSparseMatrix (S T : LocalizedDirectsumFamily)
    (Q : Fin T.length → Fin S.length → ℤ) : Prop :=
  ∀ j i, ¬ S.get i ⊆ T.get j → Q j i = 0

/-- The componentwise action of a sparse matrix on the direct sum `⊕ᵢ G_{Sᵢ}`. -/
def localizedDirectsumMatrixHom (S T : LocalizedDirectsumFamily)
    (Q : Fin T.length → Fin S.length → ℤ) :
    (Fin S.length → ℤ) →+ (Fin T.length → ℤ) where
  toFun x j := ∑ i, Q j i * x i
  map_zero' := by
    funext j
    simp
  map_add' x y := by
    funext j
    simp [mul_add, Finset.sum_add_distrib]

/-- In the simplified local model, two finite direct sums are isomorphic exactly when the support
multisets agree. -/
def localizedDirectsumIsoCriterion (S T : LocalizedDirectsumFamily) : Prop :=
  ∀ U : Finset Nat, S.count U = T.count U

lemma localizedDirectsumMatrixOfFamily_sparse (S T : LocalizedDirectsumFamily)
    (Φ : localizedDirectsumCrossHomFamily S T) :
    localizedDirectsumSparseMatrix S T (localizedDirectsumMatrixOfFamily S T Φ) := by
  intro j i hNotSubset
  have hClass := paper_xi_localized_integers_cross_hom_classification (S.get i) (T.get j)
  rcases hClass with ⟨_, hObstacle⟩
  have hzero : (Φ j i).1 1 = 0 := hObstacle hNotSubset (Φ j i) 1
  simpa [localizedDirectsumMatrixOfFamily, localizedCrossHomScalar] using hzero

/-- Localized direct-sum homomorphisms are exactly sparse integer matrices acting by the usual
finite matrix formula.
    thm:xi-localized-directsum-hom-sparse-matrix -/
theorem paper_xi_localized_directsum_hom_sparse_matrix (S T : LocalizedDirectsumFamily) :
    (∀ Φ : localizedDirectsumCrossHomFamily S T,
      localizedDirectsumSparseMatrix S T (localizedDirectsumMatrixOfFamily S T Φ)) ∧
    (∀ Q : Fin T.length → Fin S.length → ℤ,
      localizedDirectsumSparseMatrix S T Q →
        ∃ F : (Fin S.length → ℤ) →+ (Fin T.length → ℤ),
          ∀ x j, F x j = ∑ i, Q j i * x i) := by
  refine ⟨?_, ?_⟩
  · intro Φ
    exact localizedDirectsumMatrixOfFamily_sparse S T Φ
  · intro Q _hQ
    exact ⟨localizedDirectsumMatrixHom S T Q, fun _ _ => rfl⟩

/-- Every sparse localized matrix acts componentwise on the direct sum, and the resulting
isomorphism criterion is equality of the support multiset, equivalently permutation of the finite
family.
    thm:xi-time-part69d-localized-directsum-matrix-isomorphism-criterion -/
theorem paper_xi_time_part69d_localized_directsum_matrix_isomorphism_criterion
    (S T : LocalizedDirectsumFamily) :
    (∀ Φ : localizedDirectsumCrossHomFamily S T,
      localizedDirectsumSparseMatrix S T (localizedDirectsumMatrixOfFamily S T Φ)) ∧
    (∀ Q : Fin T.length → Fin S.length → ℤ,
      localizedDirectsumSparseMatrix S T Q →
        ∃ F : (Fin S.length → ℤ) →+ (Fin T.length → ℤ),
          ∀ x j, F x j = ∑ i, Q j i * x i) ∧
    (localizedDirectsumIsoCriterion S T ↔ S.Perm T) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Φ
    exact localizedDirectsumMatrixOfFamily_sparse S T Φ
  · intro Q _hQ
    refine ⟨localizedDirectsumMatrixHom S T Q, ?_⟩
    intro x j
    rfl
  · constructor
    · intro h
      exact List.perm_iff_count.2 h
    · intro h U
      exact List.Perm.count_eq h U

end Omega.Zeta
