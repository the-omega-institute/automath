import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-shifted-hankel-uniform-integrality-fourfold-equivalence`. -/
theorem paper_conclusion_shifted_hankel_uniform_integrality_fourfold_equivalence {B Lattice : Type*}
    (solvable : Nat → B → Prop) (Λ : Nat → Lattice) (unit : Lattice)
    (detHUnit detAUnit detHNextUnit : Prop)
    (h12 : ((∀ r b, solvable r b) ↔ (∀ r, Λ r = unit)))
    (h34 : ((detHUnit ∧ detAUnit) ↔ (detHUnit ∧ detHNextUnit)))
    (hbase : detHUnit ∧ detAUnit → Λ 0 = unit)
    (hstep : detAUnit → ∀ r, Λ r = unit → Λ (r + 1) = unit)
    (hdet : (∀ r, Λ r = unit) → detHUnit ∧ detAUnit) :
    ((∀ r b, solvable r b) ↔ (∀ r, Λ r = unit)) ∧
      ((∀ r, Λ r = unit) ↔ (detHUnit ∧ detAUnit)) ∧
      ((detHUnit ∧ detAUnit) ↔ (detHUnit ∧ detHNextUnit)) := by
  refine ⟨h12, ?_, h34⟩
  constructor
  · intro hΛ
    exact hdet hΛ
  · intro hUnit r
    induction r with
    | zero =>
        exact hbase hUnit
    | succ r ih =>
        exact hstep hUnit.2 r ih

end Omega.Conclusion
