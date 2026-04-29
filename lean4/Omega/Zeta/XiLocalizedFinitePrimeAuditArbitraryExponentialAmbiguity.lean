import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite-prime audit package.  The type `localized_group` indexes localizations; the
kernel invariant separates isomorphism classes, while the audited quotient invariant records the
finite quotient seen by the fixed audit. -/
structure xi_localized_finite_prime_audit_arbitrary_exponential_ambiguity_data where
  localized_group : Type
  xi_localized_finite_prime_audit_arbitrary_exponential_ambiguity_decidable_eq :
    DecidableEq localized_group
  xi_localized_finite_prime_audit_arbitrary_exponential_ambiguity_prime_kernel :
    localized_group → Finset ℕ
  xi_localized_finite_prime_audit_arbitrary_exponential_ambiguity_audited_quotient :
    localized_group → ℕ
  xi_localized_finite_prime_audit_arbitrary_exponential_ambiguity_family :
    ℕ → Finset localized_group
  xi_localized_finite_prime_audit_arbitrary_exponential_ambiguity_family_card :
    ∀ N, 1 ≤ N →
      (xi_localized_finite_prime_audit_arbitrary_exponential_ambiguity_family N).card ≥ 2 ^ N
  xi_localized_finite_prime_audit_arbitrary_exponential_ambiguity_family_kernel_rigid :
    ∀ N,
      ∀ G ∈ xi_localized_finite_prime_audit_arbitrary_exponential_ambiguity_family N,
        ∀ H ∈ xi_localized_finite_prime_audit_arbitrary_exponential_ambiguity_family N,
          G ≠ H →
          xi_localized_finite_prime_audit_arbitrary_exponential_ambiguity_prime_kernel G ≠
            xi_localized_finite_prime_audit_arbitrary_exponential_ambiguity_prime_kernel H
  xi_localized_finite_prime_audit_arbitrary_exponential_ambiguity_family_same_quotient :
    ∀ N, ∃ Q : ℕ,
      ∀ G ∈ xi_localized_finite_prime_audit_arbitrary_exponential_ambiguity_family N,
        xi_localized_finite_prime_audit_arbitrary_exponential_ambiguity_audited_quotient G = Q

namespace xi_localized_finite_prime_audit_arbitrary_exponential_ambiguity_data

/-- Prime-kernel rigidity separates every two selected localizations. -/
def pairwise_nonisomorphic
    (D : xi_localized_finite_prime_audit_arbitrary_exponential_ambiguity_data)
    (family : Finset D.localized_group) : Prop :=
  ∀ G ∈ family, ∀ H ∈ family, G ≠ H →
      D.xi_localized_finite_prime_audit_arbitrary_exponential_ambiguity_prime_kernel G ≠
        D.xi_localized_finite_prime_audit_arbitrary_exponential_ambiguity_prime_kernel H

/-- The fixed finite audit sees one common quotient on the whole family. -/
def same_audited_finite_quotient
    (D : xi_localized_finite_prime_audit_arbitrary_exponential_ambiguity_data)
    (family : Finset D.localized_group) : Prop :=
  ∃ Q : ℕ, ∀ G ∈ family,
    D.xi_localized_finite_prime_audit_arbitrary_exponential_ambiguity_audited_quotient G = Q

end xi_localized_finite_prime_audit_arbitrary_exponential_ambiguity_data

open xi_localized_finite_prime_audit_arbitrary_exponential_ambiguity_data

/-- Paper label: `cor:xi-localized-finite-prime-audit-arbitrary-exponential-ambiguity`.  For any
positive number of fresh prime coordinates, the certified hypercube family has at least `2 ^ N`
members, all with the same audited finite quotient, while prime-kernel rigidity separates their
isomorphism classes. -/
theorem paper_xi_localized_finite_prime_audit_arbitrary_exponential_ambiguity
    (D : xi_localized_finite_prime_audit_arbitrary_exponential_ambiguity_data) (N : ℕ) :
    1 ≤ N →
      ∃ family : Finset D.localized_group,
        family.card ≥ 2 ^ N ∧ D.pairwise_nonisomorphic family ∧
          D.same_audited_finite_quotient family := by
  intro hN
  letI := D.xi_localized_finite_prime_audit_arbitrary_exponential_ambiguity_decidable_eq
  refine ⟨D.xi_localized_finite_prime_audit_arbitrary_exponential_ambiguity_family N, ?_, ?_, ?_⟩
  · exact D.xi_localized_finite_prime_audit_arbitrary_exponential_ambiguity_family_card N hN
  · exact
      D.xi_localized_finite_prime_audit_arbitrary_exponential_ambiguity_family_kernel_rigid N
  · exact
      D.xi_localized_finite_prime_audit_arbitrary_exponential_ambiguity_family_same_quotient N

end Omega.Zeta
