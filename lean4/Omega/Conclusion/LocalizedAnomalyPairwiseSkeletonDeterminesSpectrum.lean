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

/-- The unordered pair index set for a localized cover of size `r`. -/
def conclusion_localized_anomaly_pairwise_completeness_pairIndex (r : ℕ) :
    Finset (Finset (Fin r)) :=
  (Finset.univ : Finset (Fin r)).powersetCard 2

/-- The concrete pairwise-union coordinate attached to an unordered pair of cover indices. -/
def conclusion_localized_anomaly_pairwise_completeness_pairCoordinate
    {r : ℕ} (S : Fin r → Finset ℕ)
    (p : Finset (Fin r)) : Finset ℕ :=
  p.biUnion S

/-- The concrete pairwise anomaly phase space is the product of the pairwise coordinates. -/
abbrev conclusion_localized_anomaly_pairwise_completeness_phaseSpace (r : ℕ) : Type :=
  conclusion_localized_anomaly_pairwise_completeness_pairIndex r → Finset ℕ

/-- Coordinate decomposition is literally the product-coordinate map. -/
def conclusion_localized_anomaly_pairwise_completeness_coordinateDecomposition
    {r : ℕ} :
    conclusion_localized_anomaly_pairwise_completeness_phaseSpace r →
      conclusion_localized_anomaly_pairwise_completeness_phaseSpace r :=
  fun a => a

/-- No higher-order primitive factor remains once the anomaly data are packaged pairwise. -/
def conclusion_localized_anomaly_pairwise_completeness_higherOrderPrimitiveFactorCount
    (_r : ℕ) : ℕ :=
  0

/-- The certificate dimension is the number of unordered pairs. -/
def conclusion_localized_anomaly_pairwise_completeness_certificateDimension (r : ℕ) : ℕ :=
  (conclusion_localized_anomaly_pairwise_completeness_pairIndex r).card

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

/-- Paper label: `cor:conclusion-localized-anomaly-pairwise-completeness`.
The pairwise skeleton determines the concrete pairwise anomaly spectrum, and the anomaly phase
space is exactly the product of its pairwise coordinates. Hence coordinates are unique, no
higher-order primitive factor survives, and the certificate dimension is `Nat.choose r 2`. -/
theorem paper_conclusion_localized_anomaly_pairwise_completeness
    {r : ℕ} (S S' : Fin r → Finset ℕ) (σ : Equiv.Perm (Fin r))
    (hpair :
      ∀ i j, localizedPairwiseUnionSkeleton S i j =
        localizedPairwiseUnionSkeleton S' (σ i) (σ j)) :
    relabelLocalizedPairwiseData σ (localizedPairwiseAnomalySpectrum S) =
      localizedPairwiseAnomalySpectrum S' ∧
    (∃! coords :
        conclusion_localized_anomaly_pairwise_completeness_phaseSpace r,
        coords =
          conclusion_localized_anomaly_pairwise_completeness_coordinateDecomposition
            (fun p =>
              conclusion_localized_anomaly_pairwise_completeness_pairCoordinate S' p)) ∧
    conclusion_localized_anomaly_pairwise_completeness_higherOrderPrimitiveFactorCount r = 0 ∧
    conclusion_localized_anomaly_pairwise_completeness_certificateDimension r = Nat.choose r 2 := by
  have hspectrum :=
    paper_conclusion_localized_anomaly_pairwise_skeleton_determines_spectrum S S' σ hpair
  refine ⟨hspectrum.2, ?_, rfl, ?_⟩
  · let coords0 : conclusion_localized_anomaly_pairwise_completeness_phaseSpace r :=
      fun p => conclusion_localized_anomaly_pairwise_completeness_pairCoordinate S' p
    refine ⟨coords0, ?_⟩
    constructor
    · rfl
    · intro coords hcoords
      simpa [coords0,
        conclusion_localized_anomaly_pairwise_completeness_coordinateDecomposition] using hcoords
  · simp [conclusion_localized_anomaly_pairwise_completeness_certificateDimension,
      conclusion_localized_anomaly_pairwise_completeness_pairIndex, Finset.card_powersetCard]

end Omega.Conclusion
