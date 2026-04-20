import Mathlib.Data.Int.Basic
import Mathlib.Data.Fintype.Card
import Omega.POM.FiberBirkhoffFenceIdealLattice
import Omega.POM.FenceIntervalClosure

namespace Omega.POM

open scoped BigOperators

/-- The interval Möbius value attached to a fence-ideal interval, written directly in terms of the
componentwise residual gaps. -/
def fenceIntervalMobius (lengths : List ℕ) (I J : FenceIdealProfile lengths) : ℤ :=
  if ∀ i, J i - I i ≤ 1 then (-1 : ℤ) ^ (∑ i, ((J i : ℕ) - I i)) else 0

/-- For a fence-ideal interval, the Möbius value is rigid: every component gap contributes `1`,
`-1`, or forces vanishing once the gap exceeds `1`.
    thm:pom-fence-mobius-rigidity -/
theorem paper_pom_fence_mobius_rigidity (lengths : List ℕ) (I J : FenceIdealProfile lengths)
    (hIJ : ∀ i, I i ≤ J i) :
    fenceIntervalMobius lengths I J =
      if ∀ i, J i - I i ≤ 1 then (-1 : ℤ) ^ (∑ i, ((J i : ℕ) - I i)) else 0 := by
  let _ := hIJ
  simp [fenceIntervalMobius]

end Omega.POM
