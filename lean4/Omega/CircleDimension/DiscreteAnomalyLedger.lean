import Mathlib.Tactic
import Omega.CircleDimension.AnomalyQuadraticLaw

namespace Omega.CircleDimension

/-- Concrete bookkeeping data for the discrete anomaly ledger of a finitely generated abelian
group `ℤ^r ⊕ F`. The maps `pTorsion` and `pRank` record the size of the `p`-torsion contribution
seen by the tensor factor and the minimal number of `p`-primary generators seen by the exterior
square factor. -/
structure DiscreteAnomalyLedgerData where
  freeRank : ℕ
  torsionRank : ℕ
  pTorsion : ℕ → ℕ
  pRank : ℕ → ℕ

namespace DiscreteAnomalyLedgerData

/-- The tensor contribution to the discrete anomaly ledger. -/
def tensorFactor (D : DiscreteAnomalyLedgerData) (p : ℕ) : ℕ :=
  D.freeRank * D.pTorsion p

/-- The exterior-square contribution is present exactly when the `p`-primary torsion is
noncyclic, modeled by `pRank p ≥ 2`. -/
def exteriorSquareFactor (D : DiscreteAnomalyLedgerData) (p : ℕ) : ℕ :=
  if 2 ≤ D.pRank p then 1 else 0

/-- The discrete part of the anomaly ledger is exactly the torsion contribution from the quadratic
law decomposition. -/
def discreteAnomalyDecomposition (D : DiscreteAnomalyLedgerData) : Prop :=
  anomalyDiscretePart D.freeRank D.torsionRank = D.torsionRank

/-- Witness that the tensor factor contributes a nontrivial `p`-primary part. -/
def tensorFactorWitness (D : DiscreteAnomalyLedgerData) (p : ℕ) : Prop :=
  0 < D.freeRank ∧ 0 < D.pTorsion p

/-- Witness that the exterior-square factor contributes a nontrivial `p`-primary part. -/
def exteriorSquareWitness (D : DiscreteAnomalyLedgerData) (p : ℕ) : Prop :=
  2 ≤ D.pRank p

/-- Nontriviality of the full discrete `p`-primary anomaly ledger. -/
def pPrimaryNontrivial (D : DiscreteAnomalyLedgerData) (p : ℕ) : Prop :=
  0 < D.tensorFactor p + D.exteriorSquareFactor p

theorem tensorFactor_pos_iff (D : DiscreteAnomalyLedgerData) (p : ℕ) :
    0 < D.tensorFactor p ↔ D.tensorFactorWitness p := by
  simp [tensorFactor, tensorFactorWitness]

theorem exteriorSquareFactor_pos_iff (D : DiscreteAnomalyLedgerData) (p : ℕ) :
    0 < D.exteriorSquareFactor p ↔ D.exteriorSquareWitness p := by
  by_cases hp : 2 ≤ D.pRank p
  · simp [exteriorSquareFactor, exteriorSquareWitness, hp]
  · simp [exteriorSquareFactor, exteriorSquareWitness, hp]

end DiscreteAnomalyLedgerData

open DiscreteAnomalyLedgerData

/-- Paper label: `prop:cdim-discrete-anomaly-ledger`. The discrete anomaly ledger is the torsion
part from the anomaly quadratic law, and its `p`-primary contribution is nontrivial exactly when
either the tensor factor or the exterior-square factor contributes. -/
theorem paper_cdim_discrete_anomaly_ledger (D : DiscreteAnomalyLedgerData) :
    D.discreteAnomalyDecomposition ∧
      ∀ p : ℕ, Nat.Prime p →
        (D.pPrimaryNontrivial p ↔ D.tensorFactorWitness p ∨ D.exteriorSquareWitness p) := by
  refine ⟨?_, ?_⟩
  · have hquad := paper_cdim_anomaly_quadratic_law D.freeRank D.torsionRank
    have hdisc := hquad.2.2.2
    simpa [DiscreteAnomalyLedgerData.discreteAnomalyDecomposition, anomalyDiscretePart] using hdisc
  · intro p hp
    have hsum :
        D.pPrimaryNontrivial p ↔ 0 < D.tensorFactor p ∨ 0 < D.exteriorSquareFactor p := by
      unfold DiscreteAnomalyLedgerData.pPrimaryNontrivial
      omega
    rw [hsum, D.tensorFactor_pos_iff, D.exteriorSquareFactor_pos_iff]

end Omega.CircleDimension
