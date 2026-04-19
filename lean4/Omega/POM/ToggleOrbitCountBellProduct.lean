import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

namespace Omega.POM

open BigOperators

/-- The truncated Bell count for a single component of size `n`: partitions of `[q]` into at
most `n` nonempty blocks. -/
def truncatedBell (q n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), Nat.stirlingSecond q k

/-- The diagonal toggle-orbit count factors across the connected components. -/
def toggleOrbitCount : List ℕ → ℕ → ℕ
  | [], _ => 1
  | n :: ns, q => truncatedBell q n * toggleOrbitCount ns q

/-- For one component, the orbit count is exactly the truncated Bell count. -/
theorem toggleOrbitCount_singleton (q n : ℕ) :
    toggleOrbitCount [n] q = truncatedBell q n := by
  simp [toggleOrbitCount]

/-- Recursive decomposition of the orbit count along the head component. -/
theorem toggleOrbitCount_cons (q n : ℕ) (componentSizes : List ℕ) :
    toggleOrbitCount (n :: componentSizes) q =
      truncatedBell q n * toggleOrbitCount componentSizes q := by
  rfl

/-- Componentwise diagonal decomposition turns the total orbit count into the product of the
single-component truncated Bell factors.
    prop:pom-toggle-orbit-count-bell-product -/
theorem paper_pom_toggle_orbit_count_bell_product (q : ℕ) (componentSizes : List ℕ) :
    toggleOrbitCount componentSizes q = (componentSizes.map (truncatedBell q)).prod := by
  induction componentSizes with
  | nil =>
      simp [toggleOrbitCount]
  | cons n ns ih =>
      simp [toggleOrbitCount, ih, List.map]

end Omega.POM
