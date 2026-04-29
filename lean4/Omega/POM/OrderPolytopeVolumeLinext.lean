import Mathlib.Data.Nat.Factorial.Basic
import Omega.POM.MaxchainsEqualsLinext

namespace Omega.POM

/-- Chapter-local wrapper for the order-polytope volume identity. -/
def OrderPolytopeVolumeLinext (P : PomFinitePoset) : Prop :=
  (Nat.factorial (Fintype.card P) : ℕ) * maxChainCount (orderIdealLattice P) =
    (Nat.factorial (Fintype.card P) : ℕ) * linearExtensionCount P

/-- Paper: `thm:pom-order-polytope-volume-linext`. -/
theorem paper_pom_order_polytope_volume_linext (P : PomFinitePoset) : OrderPolytopeVolumeLinext P := by
  simp [OrderPolytopeVolumeLinext, paper_pom_maxchains_equals_linext P]

end Omega.POM
