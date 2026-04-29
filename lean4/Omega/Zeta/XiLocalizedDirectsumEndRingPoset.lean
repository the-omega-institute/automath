import Omega.Zeta.LocalizedDirectsumMatrixIsomorphismCriterion

namespace Omega.Zeta

/-- Matrix unit in the localized direct-sum endomorphism ring. The row index is the target
summand and the column index is the source summand. -/
def xi_localized_directsum_end_ring_poset_matrixUnit (S : LocalizedDirectsumFamily)
    (j i : Fin S.length) : Fin S.length → Fin S.length → ℤ :=
  fun j' i' => if j' = j ∧ i' = i then 1 else 0

/-- Paper-facing specialization of the localized direct-sum sparse matrix theorem to endomorphisms:
endomorphism matrix units are exactly controlled by support inclusion. -/
def xi_localized_directsum_end_ring_poset_statement (S : LocalizedDirectsumFamily) : Prop :=
  (∀ Φ : localizedDirectsumCrossHomFamily S S,
    localizedDirectsumSparseMatrix S S (localizedDirectsumMatrixOfFamily S S Φ)) ∧
    (∀ Q : Fin S.length → Fin S.length → ℤ,
      localizedDirectsumSparseMatrix S S Q →
        ∃ F : (Fin S.length → ℤ) →+ (Fin S.length → ℤ),
          ∀ x j, F x j = ∑ i, Q j i * x i) ∧
      ∀ j i,
        localizedDirectsumSparseMatrix S S
            (xi_localized_directsum_end_ring_poset_matrixUnit S j i) ↔
          S.get i ⊆ S.get j

/-- Paper label: `cor:xi-localized-directsum-end-ring-poset`. -/
theorem paper_xi_localized_directsum_end_ring_poset (S : LocalizedDirectsumFamily) :
    xi_localized_directsum_end_ring_poset_statement S := by
  classical
  rcases paper_xi_localized_directsum_hom_sparse_matrix S S with ⟨hFamily, hMatrix⟩
  refine ⟨hFamily, hMatrix, ?_⟩
  intro j i
  constructor
  · intro hSparse
    by_contra hNotSubset
    have hzero := hSparse j i hNotSubset
    simp [xi_localized_directsum_end_ring_poset_matrixUnit] at hzero
  · intro hSubset j' i' hNotSubset
    by_cases hslot : j' = j ∧ i' = i
    · rcases hslot with ⟨rfl, rfl⟩
      exact False.elim (hNotSubset hSubset)
    · simp [xi_localized_directsum_end_ring_poset_matrixUnit, hslot]

end Omega.Zeta
