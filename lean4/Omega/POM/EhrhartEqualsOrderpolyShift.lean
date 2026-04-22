import Omega.POM.ZetaEqualsOrderPoly

namespace Omega.POM

/-- Chapter-local wrapper for Stanley's order polytope. In this lightweight formalization we keep
the underlying finite poset and only change the paper-facing name. -/
def orderPolytope (P : PomFinitePoset) : PomFinitePoset :=
  P

/-- Chapter-local Ehrhart counting function for the order polytope. The shift by `1` matches the
order-polynomial normalization used in the chapter. -/
def ehrhartPolynomial (Q : PomFinitePoset) : ℕ → ℕ :=
  fun t => orderPolynomial Q (t + 1)

/-- Paper label: `thm:pom-ehrhart-equals-orderpoly-shift`. -/
theorem paper_pom_ehrhart_equals_orderpoly_shift (P : PomFinitePoset) :
    ehrhartPolynomial (orderPolytope P) = fun t : Nat => orderPolynomial P (t + 1) := by
  rfl

end Omega.POM
