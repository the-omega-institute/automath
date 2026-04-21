import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic
import Omega.Conclusion.LocalizedPairwiseUnionWedgeBilinearization

namespace Omega.Conclusion

/-- The pairwise-union skeleton attached to a finite localized cover. -/
def localizedPairwiseUnionSkeleton {r : ℕ} (S : Fin r → Finset ℕ) (i j : Fin r) : Finset ℕ :=
  S i ∪ S j

/-- The corresponding pairwise anomaly spectrum, recorded here by the cardinalities of the
pairwise-union factors. -/
def localizedPairwiseAnomalySpectrum {r : ℕ} (S : Fin r → Finset ℕ) (i j : Fin r) : ℕ :=
  (localizedPairwiseUnionSkeleton S i j).card

/-- Reindex a pairwise object by a permutation of the localized cover. -/
def relabelLocalizedPairwiseData {r : ℕ} {α : Type*} (σ : Equiv.Perm (Fin r))
    (F : Fin r → Fin r → α) : Fin r → Fin r → α :=
  fun i j => F (σ.symm i) (σ.symm j)

/-- Paper label: `thm:conclusion-localized-anomaly-pairwise-skeleton-determines-spectrum`.

If the pairwise-union skeletons agree after relabeling by a permutation of the cover, then the
induced pairwise anomaly spectra agree as well; equivalently, the permutation transports the full
product-indexed spectrum from one localized cover to the other. -/
theorem paper_conclusion_localized_anomaly_pairwise_skeleton_determines_spectrum
    {r : ℕ} (S S' : Fin r → Finset ℕ) (σ : Equiv.Perm (Fin r))
    (hpair :
      ∀ i j, localizedPairwiseUnionSkeleton S i j =
        localizedPairwiseUnionSkeleton S' (σ i) (σ j)) :
    relabelLocalizedPairwiseData σ (localizedPairwiseUnionSkeleton S) =
      localizedPairwiseUnionSkeleton S' ∧
    relabelLocalizedPairwiseData σ (localizedPairwiseAnomalySpectrum S) =
      localizedPairwiseAnomalySpectrum S' := by
  have hpack :=
    paper_conclusion_localized_pairwise_union_wedge_bilinearization
      (∅) (∅)
      (∀ i j, localizedPairwiseUnionSkeleton S i j =
        localizedPairwiseUnionSkeleton S' (σ i) (σ j))
      True True hpair trivial trivial
  refine ⟨?_, ?_⟩
  · funext i j
    simpa [relabelLocalizedPairwiseData] using hpack.1 (σ.symm i) (σ.symm j)
  · funext i j
    simp [localizedPairwiseAnomalySpectrum, relabelLocalizedPairwiseData]
    simpa [relabelLocalizedPairwiseData] using congrArg Finset.card (hpack.1 (σ.symm i) (σ.symm j))

end Omega.Conclusion
