import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmKappaSquareCubicFieldS3
import Omega.Zeta.XiTerminalZmStokesLeyangCommonQuadraticResolvent

namespace Omega.Zeta

/-- Concrete certificates for the local-cumulant quadratic branch, the Lee-Yang cubic branch,
and their intersection. -/
structure xi_time_part62a_local_cumulant_branch_cubic_linear_disjointness_data where
  xi_time_part62a_local_cumulant_branch_cubic_linear_disjointness_quadraticDegree : ℕ
  xi_time_part62a_local_cumulant_branch_cubic_linear_disjointness_cubicDegree : ℕ
  xi_time_part62a_local_cumulant_branch_cubic_linear_disjointness_intersectionDegree : ℕ
  xi_time_part62a_local_cumulant_branch_cubic_linear_disjointness_quadraticDegree_eq :
    xi_time_part62a_local_cumulant_branch_cubic_linear_disjointness_quadraticDegree = 2
  xi_time_part62a_local_cumulant_branch_cubic_linear_disjointness_cubicDegree_eq :
    xi_time_part62a_local_cumulant_branch_cubic_linear_disjointness_cubicDegree = 3
  xi_time_part62a_local_cumulant_branch_cubic_linear_disjointness_intersectionDegree_eq :
    xi_time_part62a_local_cumulant_branch_cubic_linear_disjointness_intersectionDegree = 1

namespace xi_time_part62a_local_cumulant_branch_cubic_linear_disjointness_data

/-- The audited local-cumulant quadratic-field certificate. -/
def localCumulantQuadraticCertificate
    (_D : xi_time_part62a_local_cumulant_branch_cubic_linear_disjointness_data) : Prop :=
  xiTerminalStokesLeyangQuadraticResolventDiscriminant = -111 ∧
    xiTerminalStokesLeyangSharedArtinDimension = 2

/-- The audited Lee-Yang cubic-field certificate. -/
def leeyangCubicCertificate
    (_D : xi_time_part62a_local_cumulant_branch_cubic_linear_disjointness_data) : Prop :=
  xiTerminalKappaSquareS3Audit

/-- The intersection certificate used to compute the compositum degree. -/
def intersectionCertificate
    (D : xi_time_part62a_local_cumulant_branch_cubic_linear_disjointness_data) : Prop :=
  D.xi_time_part62a_local_cumulant_branch_cubic_linear_disjointness_intersectionDegree = 1

/-- Degree of the compositum predicted by the two certificates and their trivial intersection. -/
def compositumDegree
    (D : xi_time_part62a_local_cumulant_branch_cubic_linear_disjointness_data) : ℕ :=
  D.xi_time_part62a_local_cumulant_branch_cubic_linear_disjointness_quadraticDegree *
    D.xi_time_part62a_local_cumulant_branch_cubic_linear_disjointness_cubicDegree /
      D.xi_time_part62a_local_cumulant_branch_cubic_linear_disjointness_intersectionDegree

/-- No nontrivial degree can divide both the quadratic and cubic branch degrees. -/
def commonDegreeExclusion
    (_D : xi_time_part62a_local_cumulant_branch_cubic_linear_disjointness_data) : Prop :=
  ∀ d : ℕ, d ∣ 2 → d ∣ 3 → d = 1

/-- Paper-facing linear-disjointness conclusion. -/
def linearDisjointness
    (D : xi_time_part62a_local_cumulant_branch_cubic_linear_disjointness_data) : Prop :=
  D.localCumulantQuadraticCertificate ∧
    D.leeyangCubicCertificate ∧
      D.intersectionCertificate ∧
        D.compositumDegree = 6 ∧ D.commonDegreeExclusion

end xi_time_part62a_local_cumulant_branch_cubic_linear_disjointness_data

/-- Paper label:
`thm:xi-time-part62a-local-cumulant-branch-cubic-linear-disjointness`. The existing quadratic
resolvent and Lee-Yang cubic certificates give degrees `2` and `3`; the supplied intersection
certificate makes the compositum degree `6`, and coprimality excludes a nontrivial common
subdegree. -/
theorem paper_xi_time_part62a_local_cumulant_branch_cubic_linear_disjointness
    (D : xi_time_part62a_local_cumulant_branch_cubic_linear_disjointness_data) :
    D.linearDisjointness := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨paper_xi_terminal_zm_stokes_leyang_common_quadratic_resolvent.2.2,
      paper_xi_terminal_zm_stokes_leyang_shared_artin_representation.2.2.2.2.1⟩
  · exact paper_xi_terminal_zm_kappa_square_cubic_field_s3.2.2.2.2
  · exact
      D.xi_time_part62a_local_cumulant_branch_cubic_linear_disjointness_intersectionDegree_eq
  · simp [xi_time_part62a_local_cumulant_branch_cubic_linear_disjointness_data.compositumDegree,
      D.xi_time_part62a_local_cumulant_branch_cubic_linear_disjointness_quadraticDegree_eq,
      D.xi_time_part62a_local_cumulant_branch_cubic_linear_disjointness_cubicDegree_eq,
      D.xi_time_part62a_local_cumulant_branch_cubic_linear_disjointness_intersectionDegree_eq]
  · intro d hd2 hd3
    exact Nat.dvd_one.mp (by simpa using Nat.dvd_gcd hd2 hd3)

end Omega.Zeta
