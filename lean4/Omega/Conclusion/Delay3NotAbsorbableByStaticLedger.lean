import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete single-pass depth and static-ledger capacity data for the delay-three obstruction. -/
structure conclusion_delay3_not_absorbable_by_static_ledger_Data where
  conclusion_delay3_not_absorbable_by_static_ledger_singlePassCausalDepth : ℕ
  conclusion_delay3_not_absorbable_by_static_ledger_staticLedgerCapacity : ℕ

namespace conclusion_delay3_not_absorbable_by_static_ledger_Data

/-- A static ledger strictification would have to absorb a delay-three causal reserve. -/
def staticLedgerStrictification
    (D : conclusion_delay3_not_absorbable_by_static_ledger_Data) : Prop :=
  D.conclusion_delay3_not_absorbable_by_static_ledger_staticLedgerCapacity + 3 ≤
    D.conclusion_delay3_not_absorbable_by_static_ledger_singlePassCausalDepth

/-- The residual online delay lower bound remains after subtracting static ledger capacity. -/
def delayLowerBoundPersists
    (D : conclusion_delay3_not_absorbable_by_static_ledger_Data) : Prop :=
  3 ≤
    D.conclusion_delay3_not_absorbable_by_static_ledger_singlePassCausalDepth -
      D.conclusion_delay3_not_absorbable_by_static_ledger_staticLedgerCapacity

end conclusion_delay3_not_absorbable_by_static_ledger_Data

/-- Paper label: `cor:conclusion-delay3-not-absorbable-by-static-ledger`. -/
theorem paper_conclusion_delay3_not_absorbable_by_static_ledger
    (D : conclusion_delay3_not_absorbable_by_static_ledger_Data) :
    D.staticLedgerStrictification → D.delayLowerBoundPersists := by
  intro hStrict
  unfold conclusion_delay3_not_absorbable_by_static_ledger_Data.staticLedgerStrictification at hStrict
  unfold conclusion_delay3_not_absorbable_by_static_ledger_Data.delayLowerBoundPersists
  omega

end Omega.Conclusion
