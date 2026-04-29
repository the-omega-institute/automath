import Mathlib.Data.Nat.Basic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-zero-curvature-tower-canonical-strictification-uniqueness`. -/
theorem paper_conclusion_zero_curvature_tower_canonical_strictification_uniqueness
    (n : ℕ) (globalZero towerUnique : Prop) (localZero localUnique : Fin n → Prop)
    (hLocal : globalZero → ∀ k, localZero k)
    (hUnique : ∀ k, localZero k → localUnique k)
    (hTower : (∀ k, localUnique k) → towerUnique) :
    globalZero → towerUnique := by
  intro hGlobal
  apply hTower
  intro k
  exact hUnique k (hLocal hGlobal k)

end Omega.Conclusion
