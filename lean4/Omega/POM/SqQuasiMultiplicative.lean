import Omega.Folding.MomentBounds

namespace Omega.POM

/-- Paper label: `prop:pom-sq-quasi-multiplicative`. This chapter-level wrapper exposes the
quadratic collision-moment power bound already formalized in the folding development. -/
theorem paper_pom_sq_quasi_multiplicative (q m : ℕ) (hq : 1 ≤ q) :
    Omega.momentSum 2 m ^ q ≤ Omega.momentSum (2 * q) m * Nat.fib (m + 2) ^ (q - 1) := by
  exact Omega.momentSum_two_pow_le q m hq

end Omega.POM
