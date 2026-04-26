import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- Fiberwise plus/minus multiplicity data for the fold-gauge decomposition. -/
structure conclusion_fold_gauge_commutant_matrix_sector_signedFiber where
  plusDim : ℕ
  minusDim : ℕ

/-- Each nontrivial complementary fiber contributes one scalar block to the commutant. -/
def conclusion_fold_gauge_commutant_matrix_sector_complementScalarRank
    (F : conclusion_fold_gauge_commutant_matrix_sector_signedFiber) : ℕ :=
  if F.plusDim + F.minusDim = 0 then 0 else 1

/-- Indexing set for the full visible matrix block. -/
abbrev conclusion_fold_gauge_commutant_matrix_sector_visibleMatrixSector (n : ℕ) :=
  Fin n × Fin n

/-- Indexing set for the scalar complements attached to the fiberwise plus/minus decomposition. -/
abbrev conclusion_fold_gauge_commutant_matrix_sector_scalarFiberSector
    {n : ℕ} (fibers : Fin n → conclusion_fold_gauge_commutant_matrix_sector_signedFiber) :=
  Σ i : Fin n, Fin (conclusion_fold_gauge_commutant_matrix_sector_complementScalarRank (fibers i))

/-- Concrete finite data for the fold-gauge commutant package. The commutant is modeled by a
finite indexing type together with an explicit block decomposition into the visible matrix sector
and the scalar fiber-complement sector. -/
structure FoldGaugeCommutantMatrixSectorData where
  visibleFiberCount : ℕ
  fiberDecomposition :
    Fin visibleFiberCount → conclusion_fold_gauge_commutant_matrix_sector_signedFiber
  commutantIndex : Type
  commutantFintype : Fintype commutantIndex
  blockDecomposition :
    commutantIndex ≃
      (conclusion_fold_gauge_commutant_matrix_sector_visibleMatrixSector visibleFiberCount ⊕
        conclusion_fold_gauge_commutant_matrix_sector_scalarFiberSector fiberDecomposition)

/-- The commutant splits as the visible full matrix sector plus one scalar complement for every
nontrivial fiberwise plus/minus complement. -/
def FoldGaugeCommutantMatrixSectorStatement (D : FoldGaugeCommutantMatrixSectorData) : Prop :=
  let _ := D.commutantFintype
  Nonempty
        (D.commutantIndex ≃
          (conclusion_fold_gauge_commutant_matrix_sector_visibleMatrixSector D.visibleFiberCount ⊕
            conclusion_fold_gauge_commutant_matrix_sector_scalarFiberSector D.fiberDecomposition)) ∧
      Fintype.card D.commutantIndex =
        D.visibleFiberCount ^ 2 +
          ∑ i : Fin D.visibleFiberCount,
            conclusion_fold_gauge_commutant_matrix_sector_complementScalarRank
              (D.fiberDecomposition i)

/-- Paper label: `thm:conclusion-fold-gauge-commutant-matrix-sector`. -/
theorem paper_conclusion_fold_gauge_commutant_matrix_sector
    (D : FoldGaugeCommutantMatrixSectorData) : FoldGaugeCommutantMatrixSectorStatement D := by
  let _ := D.commutantFintype
  refine ⟨⟨D.blockDecomposition⟩, ?_⟩
  simpa [FoldGaugeCommutantMatrixSectorStatement, pow_two,
    conclusion_fold_gauge_commutant_matrix_sector_visibleMatrixSector,
    conclusion_fold_gauge_commutant_matrix_sector_scalarFiberSector] using
    Fintype.card_congr D.blockDecomposition

end Omega.Conclusion
