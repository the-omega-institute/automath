import Omega.Zeta.DerivedZGHardcoreFactorization
import Omega.Zeta.DerivedZGNoScalarEulerProduct
import Omega.Zeta.XiZGHardcoreConstantResidue

namespace Omega.DerivedConsequences

open Omega.Zeta

/-- The ZG Tauberian package extracted from the already formalized hard-core factorization:
the hard-core factor stays positive, bounded by `1`, and gives the Euler-quotient factorization
for the stabilized Dirichlet value. -/
def derived_zg_tauberian_complete_euler_irreducible_tauberian_complete : Prop :=
  ∀ D : DerivedZGHardcoreFactorizationData,
    0 < D.hardcoreLimit ∧
      D.hardcoreLimit ≤ 1 ∧
        D.dirichletValue = D.zetaEulerQuotient * D.hardcoreLimit

/-- The concrete residue normalization at the critical point for the standard ZG hard-core
factorization witness. -/
def derived_zg_tauberian_complete_euler_irreducible_critical_residue : Prop :=
  let D := xi_zg_hardcore_constant_residue_factorization_data
  let W := xi_zg_hardcore_constant_residue_witness
  W.analytic.residueAtOne = D.hardcoreLimit / D.zetaEulerQuotient

/-- Combined Tauberian-completeness / Euler-irreducibility statement. -/
def derived_zg_tauberian_complete_euler_irreducible_statement : Prop :=
  derived_zg_tauberian_complete_euler_irreducible_tauberian_complete ∧
    derived_zg_tauberian_complete_euler_irreducible_critical_residue ∧
      derivedZGNoScalarEulerProduct

/-- Paper label: `thm:derived-zg-tauberian-complete-euler-irreducible`. The finite-support
hard-core factorization already provides the positive Tauberian factor and its stabilized Euler
quotient identity, the residue theorem identifies the critical constant, and the squarefree /
single-prime coefficient comparison forces every putative scalar local factor to be `1 + T`,
contradicting the vanishing adjacent-prime coefficient. -/
theorem paper_derived_zg_tauberian_complete_euler_irreducible :
    derived_zg_tauberian_complete_euler_irreducible_statement := by
  refine ⟨?_, ?_, paper_derived_zg_no_scalar_euler_product⟩
  · intro D
    rcases paper_derived_zg_hardcore_factorization D with ⟨_, _, _, _, _, hpos, hle, hvalue⟩
    exact ⟨hpos, hle, hvalue⟩
  · dsimp [derived_zg_tauberian_complete_euler_irreducible_critical_residue]
    rcases (by
      simpa [xi_zg_hardcore_constant_residue_statement] using
        paper_xi_zg_hardcore_constant_residue) with ⟨_, _, _, hresidue⟩
    exact hresidue

end Omega.DerivedConsequences
