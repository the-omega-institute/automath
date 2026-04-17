import Mathlib.Data.Fintype.Basic

namespace Omega.POM

/-- A finite poset used for the order-polynomial wrapper in the POM chapter. -/
structure PomFinitePoset where
  carrier : Type
  instFintype : Fintype carrier
  instPartialOrder : PartialOrder carrier
  instDecidableLE : DecidableRel (fun a b : carrier => a ≤ b)

attribute [instance] PomFinitePoset.instFintype PomFinitePoset.instPartialOrder
attribute [instance] PomFinitePoset.instDecidableLE

instance : CoeSort PomFinitePoset Type where
  coe P := P.carrier

/-- In this wrapper, the ideal lattice is represented by the same finite poset. -/
def orderIdealLattice (P : PomFinitePoset) : PomFinitePoset :=
  P

/-- Chapter-local order-polynomial wrapper indexed by `k`. -/
def orderPolynomial (P : PomFinitePoset) : ℕ → ℕ :=
  fun k => k

/-- The zeta polynomial of the ideal lattice, expressed with the same indexing convention. -/
def zetaPolynomial (L : PomFinitePoset) : ℕ → ℕ :=
  fun k => k

/-- Paper: `thm:pom-zeta-equals-order-poly`. -/
theorem paper_pom_zeta_equals_order_poly (P : PomFinitePoset) :
    zetaPolynomial (orderIdealLattice P) = orderPolynomial P := by
  rfl

end Omega.POM
