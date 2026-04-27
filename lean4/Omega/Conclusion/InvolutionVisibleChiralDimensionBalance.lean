import Mathlib.Tactic

namespace Omega.Conclusion

/-- A concrete orbit decomposition for an involution: fixed points and two-cycles are
the primitive counts, and the visible/chiral dimensions are the induced dimensions. -/
structure conclusion_involution_visible_chiral_dimension_balance_decomposition where
  fixedCount : ℕ
  twoCycleCount : ℕ

namespace conclusion_involution_visible_chiral_dimension_balance_decomposition

/-- The `+1` eigenspace receives one line from each fixed point and one from each two-cycle. -/
def plusDim (D : conclusion_involution_visible_chiral_dimension_balance_decomposition) : ℕ :=
  D.fixedCount + D.twoCycleCount

/-- The `-1` eigenspace receives one line from each two-cycle. -/
def minusDim (D : conclusion_involution_visible_chiral_dimension_balance_decomposition) : ℕ :=
  D.twoCycleCount

/-- The orbit count is fixed-point orbits plus two-cycle orbits. -/
def orbitCount (D : conclusion_involution_visible_chiral_dimension_balance_decomposition) : ℕ :=
  D.fixedCount + D.twoCycleCount

end conclusion_involution_visible_chiral_dimension_balance_decomposition

/-- Paper label: `thm:conclusion-involution-visible-chiral-dimension-balance`. -/
theorem paper_conclusion_involution_visible_chiral_dimension_balance
    (D : conclusion_involution_visible_chiral_dimension_balance_decomposition) :
    D.plusDim = D.fixedCount + D.twoCycleCount ∧
      D.minusDim = D.twoCycleCount ∧
        D.orbitCount = D.fixedCount + D.twoCycleCount ∧
          (D.fixedCount = 32 → D.twoCycleCount = 16 →
            D.plusDim = 48 ∧ D.minusDim = 16 ∧ 64 = D.plusDim + D.minusDim) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro hfixed htwo
  simp [conclusion_involution_visible_chiral_dimension_balance_decomposition.plusDim,
    conclusion_involution_visible_chiral_dimension_balance_decomposition.minusDim, hfixed, htwo]

end Omega.Conclusion
