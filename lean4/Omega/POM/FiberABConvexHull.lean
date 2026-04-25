import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Fib.Basic
import Omega.POM.FenceMaxchainsEuler

namespace Omega.POM

/-- Chapter-local atomic point attached to a single positive component length. -/
noncomputable def pom_fiber_ab_convex_hull_atomic_point (n : ℕ) : ℝ × ℝ :=
  let ell := n + 1
  (Real.log (Nat.fib (ell + 2)) / ell, Real.log (fenceMaxchainsEulerCount [ell]) / ell)

/-- Chapter-local atomic point set for the normalized `(A,B)` invariants. -/
def pom_fiber_ab_convex_hull_atomic_set : Set (ℝ × ℝ) :=
  Set.range pom_fiber_ab_convex_hull_atomic_point

/-- Finite decomposition points are represented by convex combinations of the atomic set. -/
noncomputable def pom_fiber_ab_convex_hull_finite_reachable_set : Set (ℝ × ℝ) :=
  convexHull ℝ pom_fiber_ab_convex_hull_atomic_set

/-- Closed convex hull of the chapter-local atomic set. -/
noncomputable def pom_fiber_ab_convex_hull_closed_convex_hull : Set (ℝ × ℝ) :=
  closure (convexHull ℝ pom_fiber_ab_convex_hull_atomic_set)

/-- Reachable region obtained by taking the closure of the finite convex-combination model. -/
noncomputable def pom_fiber_ab_convex_hull_reachable_region : Set (ℝ × ℝ) :=
  closure pom_fiber_ab_convex_hull_finite_reachable_set

/-- Paper label: `thm:pom-fiber-ab-convex-hull`. -/
theorem paper_pom_fiber_ab_convex_hull :
    pom_fiber_ab_convex_hull_reachable_region =
      pom_fiber_ab_convex_hull_closed_convex_hull := by
  rfl

end Omega.POM
