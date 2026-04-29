import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite-prime audit data: a finite audited window and an injective supply of fresh
prime labels outside it.  The labels are natural-number stand-ins for prime coordinates. -/
structure xi_localized_finite_prime_audit_exponential_incompleteness_data where
  auditWindow : Finset ℕ
  freshPrime : ℕ → ℕ
  freshPrime_not_mem_audit : ∀ i, freshPrime i ∉ auditWindow
  freshPrime_injective : Function.Injective freshPrime

/-- The finite set of extra fresh labels selected by a subset of the audit index window. -/
def xi_localized_finite_prime_audit_exponential_incompleteness_extra
    (D : xi_localized_finite_prime_audit_exponential_incompleteness_data) (N : ℕ)
    (E : Finset (Fin N)) : Finset ℕ :=
  E.image fun i => D.freshPrime i.1

/-- The localized support `T ∪ {q_i : i ∈ E}`. -/
def xi_localized_finite_prime_audit_exponential_incompleteness_support
    (D : xi_localized_finite_prime_audit_exponential_incompleteness_data) (N : ℕ)
    (E : Finset (Fin N)) : Finset ℕ :=
  D.auditWindow ∪
    xi_localized_finite_prime_audit_exponential_incompleteness_extra D N E

/-- The audited finite kernel only sees the original audit window. -/
def xi_localized_finite_prime_audit_exponential_incompleteness_auditedKernel
    (D : xi_localized_finite_prime_audit_exponential_incompleteness_data) (N : ℕ)
    (E : Finset (Fin N)) : Finset ℕ :=
  xi_localized_finite_prime_audit_exponential_incompleteness_support D N E ∩ D.auditWindow

/-- The finite-rank circle dimension of every finite localization in this model. -/
def xi_localized_finite_prime_audit_exponential_incompleteness_cdim
    (_D : xi_localized_finite_prime_audit_exponential_incompleteness_data) (_N : ℕ)
    (_E : Finset (Fin _N)) : ℕ :=
  1

/-- The rigidity relation: two localized models are isomorphic exactly when their supports agree. -/
def xi_localized_finite_prime_audit_exponential_incompleteness_isomorphic
    (D : xi_localized_finite_prime_audit_exponential_incompleteness_data) (N : ℕ)
    (E E' : Finset (Fin N)) : Prop :=
  xi_localized_finite_prime_audit_exponential_incompleteness_support D N E =
    xi_localized_finite_prime_audit_exponential_incompleteness_support D N E'

lemma xi_localized_finite_prime_audit_exponential_incompleteness_fresh_mem_support_iff
    (D : xi_localized_finite_prime_audit_exponential_incompleteness_data) (N : ℕ)
    (E : Finset (Fin N)) (i : Fin N) :
    D.freshPrime i.1 ∈
        xi_localized_finite_prime_audit_exponential_incompleteness_support D N E ↔
      i ∈ E := by
  constructor
  · intro hmem
    simp [xi_localized_finite_prime_audit_exponential_incompleteness_support,
      xi_localized_finite_prime_audit_exponential_incompleteness_extra] at hmem
    rcases hmem with haudit | himage
    · exact (D.freshPrime_not_mem_audit i.1 haudit).elim
    · rcases himage with ⟨j, hj, hji⟩
      have hnat : j.1 = i.1 := D.freshPrime_injective hji
      have hfin : j = i := Fin.ext hnat
      simpa [hfin] using hj
  · intro hi
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨i, hi, rfl⟩))

lemma xi_localized_finite_prime_audit_exponential_incompleteness_support_injective
    (D : xi_localized_finite_prime_audit_exponential_incompleteness_data) (N : ℕ) :
    Function.Injective
      (xi_localized_finite_prime_audit_exponential_incompleteness_support D N) := by
  intro E E' hsupport
  ext i
  have hpoint :
      D.freshPrime i.1 ∈
          xi_localized_finite_prime_audit_exponential_incompleteness_support D N E ↔
        D.freshPrime i.1 ∈
          xi_localized_finite_prime_audit_exponential_incompleteness_support D N E' := by
    rw [hsupport]
  simpa [
    xi_localized_finite_prime_audit_exponential_incompleteness_fresh_mem_support_iff D N E i,
    xi_localized_finite_prime_audit_exponential_incompleteness_fresh_mem_support_iff D N E' i]
    using hpoint

/-- Concrete statement for the finite audit incompleteness theorem.  The candidate family is the
powerset of `Fin N`, so it has `2^N` members; all candidates have the same audited kernel and
circle dimension, while support rigidity separates distinct subsets. -/
def xi_localized_finite_prime_audit_exponential_incompleteness_statement
    (D : xi_localized_finite_prime_audit_exponential_incompleteness_data) (N : ℕ) : Prop :=
  Fintype.card (Finset (Fin N)) = 2 ^ N ∧
    (∀ E : Finset (Fin N),
      xi_localized_finite_prime_audit_exponential_incompleteness_cdim D N E = 1) ∧
    (∀ E : Finset (Fin N),
      xi_localized_finite_prime_audit_exponential_incompleteness_auditedKernel D N E =
        D.auditWindow) ∧
    ∀ E E' : Finset (Fin N),
      xi_localized_finite_prime_audit_exponential_incompleteness_isomorphic D N E E' ↔ E = E'

/-- Paper label: `thm:xi-localized-finite-prime-audit-exponential-incompleteness`. -/
theorem paper_xi_localized_finite_prime_audit_exponential_incompleteness
    (D : xi_localized_finite_prime_audit_exponential_incompleteness_data) (N : Nat) :
    xi_localized_finite_prime_audit_exponential_incompleteness_statement D N := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp
  · intro E
    rfl
  · intro E
    ext p
    simp [xi_localized_finite_prime_audit_exponential_incompleteness_auditedKernel,
      xi_localized_finite_prime_audit_exponential_incompleteness_support]
  · intro E E'
    constructor
    · intro h
      exact xi_localized_finite_prime_audit_exponential_incompleteness_support_injective D N h
    · intro h
      simp [xi_localized_finite_prime_audit_exponential_incompleteness_isomorphic, h]

end Omega.Zeta
