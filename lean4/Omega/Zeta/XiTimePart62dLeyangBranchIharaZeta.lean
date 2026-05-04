import Mathlib.Tactic
import Omega.Zeta.DerivedLeyangBranchsetIharaZeta

namespace Omega.Zeta

open Finset
open scoped BigOperators

/-- Vertex count for the five Lee--Yang branch hypercube components. -/
def xi_time_part62d_leyang_branch_ihara_zeta_vertexCount (n : ℕ) : ℕ :=
  5 * 2 ^ (2 * n)

/-- Edge count for the five Lee--Yang branch hypercube components. -/
def xi_time_part62d_leyang_branch_ihara_zeta_edgeCount (n : ℕ) : ℕ :=
  5 * ((2 * n) * 2 ^ (2 * n - 1))

/-- Ihara--Bass excess exponent for the five-component branch graph. -/
def xi_time_part62d_leyang_branch_ihara_zeta_bassExponent (n : ℕ) : ℕ :=
  5 * ((2 * n - 2) * 2 ^ (2 * n - 1))

/-- Concrete finite-product certificate for the Lee--Yang branch Ihara zeta denominator. -/
def xi_time_part62d_leyang_branch_ihara_zeta_statement : Prop :=
  ∀ n : ℕ,
    DerivedLeyangBranchsetIharaZetaClosedForm n ∧
      xi_time_part62d_leyang_branch_ihara_zeta_vertexCount n = 5 * 2 ^ (2 * n) ∧
      xi_time_part62d_leyang_branch_ihara_zeta_edgeCount n =
        5 * ((2 * n) * 2 ^ (2 * n - 1)) ∧
      xi_time_part62d_leyang_branch_ihara_zeta_bassExponent n =
        5 * ((2 * n - 2) * 2 ^ (2 * n - 1)) ∧
      (∀ j ∈ range (2 * n + 1),
        leyangBranchsetMultiplicity n j = 5 * Nat.choose (2 * n) j)

/-- Paper label: `thm:xi-time-part62d-leyang-branch-ihara-zeta`. -/
theorem paper_xi_time_part62d_leyang_branch_ihara_zeta :
    xi_time_part62d_leyang_branch_ihara_zeta_statement := by
  intro n
  refine ⟨paper_derived_leyang_branchset_ihara_zeta n, rfl, rfl, rfl, ?_⟩
  intro j _hj
  rfl

end Omega.Zeta
