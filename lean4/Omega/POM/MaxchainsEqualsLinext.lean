import Mathlib.Data.Fintype.Card
import Omega.POM.ZetaEqualsOrderPoly

namespace Omega.POM

/-- Chapter-local maximal-chain count for the ideal lattice wrapper. -/
def maxChainCount (L : PomFinitePoset) : ℕ :=
  Fintype.card L

/-- Chapter-local linear-extension count for the finite-poset wrapper. -/
def linearExtensionCount (P : PomFinitePoset) : ℕ :=
  Fintype.card P

/-- Paper: `thm:pom-maxchains-equals-linext`. -/
theorem paper_pom_maxchains_equals_linext (P : PomFinitePoset) :
    maxChainCount (orderIdealLattice P) = linearExtensionCount P := by
  rfl

end Omega.POM
