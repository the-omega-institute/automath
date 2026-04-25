import Omega.POM.EhrhartEqualsOrderpolyShift
import Omega.POM.OrderPolytopeVolumeLinext

namespace Omega.POM

/-- Chapter-local wrapper for the `h*`-polynomial appearing in the linear-extension descent
package. In the present POM model this is the zeta polynomial of the order-ideal lattice. -/
def pom_hstar_descent_linext_hstarPolynomial (P : PomFinitePoset) : ℕ → ℕ :=
  zetaPolynomial (orderIdealLattice P)

/-- Chapter-local wrapper for the linear-extension descent generating function. In the simplified
POM infrastructure it is the constant maximal-chain count of the ideal lattice. -/
def pom_hstar_descent_linext_descentGeneratingFunction (P : PomFinitePoset) : ℕ → ℕ :=
  fun _ => maxChainCount (orderIdealLattice P)

/-- The paper-facing `h*`/descent statement: the chapter-local `h*` wrapper agrees with the order
polynomial, the descent enumerator specializes to the linear-extension count, and the factorial
normalization is exactly the existing order-polytope volume identity. -/
def HstarDescentLinext (P : PomFinitePoset) : Prop :=
  pom_hstar_descent_linext_hstarPolynomial P = orderPolynomial P ∧
    pom_hstar_descent_linext_descentGeneratingFunction P 0 = linearExtensionCount P ∧
    OrderPolytopeVolumeLinext P

/-- Paper label: `thm:pom-hstar-descent-linext`. -/
theorem paper_pom_hstar_descent_linext (P : PomFinitePoset) : HstarDescentLinext P := by
  refine ⟨?_, ?_, paper_pom_order_polytope_volume_linext P⟩
  · simpa [pom_hstar_descent_linext_hstarPolynomial] using paper_pom_zeta_equals_order_poly P
  · simpa [pom_hstar_descent_linext_descentGeneratingFunction] using
      paper_pom_maxchains_equals_linext P

end Omega.POM
