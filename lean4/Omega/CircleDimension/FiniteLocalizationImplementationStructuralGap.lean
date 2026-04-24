import Omega.CircleDimension.FiniteLocalizationDirectsumPrimeLedgerExactSequence

namespace Omega.CircleDimension

/-- After identifying the implementation half-circle dimension with `1/2` and the structural
circle dimension with `a + r`, the claimed structural gap is just arithmetic in `ℚ`.
    cor:cdim-implementation-structural-gap-for-finite-localization-ledgers -/
theorem paper_cdim_implementation_structural_gap_for_finite_localization_ledgers
    (a r : ℕ) (hpos : 0 < a + r) (impl structural : ℚ) (hImpl : impl = 1 / 2)
    (hStructural : structural = a + r) : structural - impl = a + r - 1 / 2 := by
  let _ := hpos
  rw [hImpl, hStructural]

end Omega.CircleDimension
