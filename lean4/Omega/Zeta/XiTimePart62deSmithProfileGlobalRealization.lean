import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite local Smith-profile data.  For each prime `p` and diagonal index `i`,
`localExponent p i` is the requested `p`-adic Smith exponent; all nonzero local data are supported
on the finite prime set `support`, and the profiles are monotone along the diagonal. -/
structure xi_time_part62de_smith_profile_global_realization_data where
  rank : ℕ
  support : Finset ℕ
  localExponent : ℕ → Fin rank → ℕ
  support_spec : ∀ p, p ∉ support → ∀ i, localExponent p i = 0
  support_prime : ∀ p ∈ support, Nat.Prime p
  monotone : ∀ p i j, i ≤ j → localExponent p i ≤ localExponent p j

/-- The finitely supported exponent profile for one diagonal slot. -/
noncomputable def xi_time_part62de_smith_profile_global_realization_profile
    (D : xi_time_part62de_smith_profile_global_realization_data) (i : Fin D.rank) :
    ℕ →₀ ℕ :=
  Finsupp.onFinset D.support (fun p => D.localExponent p i) fun p hp => by
    exact Classical.not_not.mp fun hmem => hp (D.support_spec p hmem i)

/-- The global diagonal entry obtained by multiplying all local prime powers. -/
noncomputable def xi_time_part62de_smith_profile_global_realization_diagonalEntry
    (D : xi_time_part62de_smith_profile_global_realization_data) (i : Fin D.rank) : ℕ :=
  (xi_time_part62de_smith_profile_global_realization_profile D i).prod (fun p e => p ^ e)

/-- The paper-facing concrete realization statement: the constructed diagonal entries have the
requested local valuation profiles, form a divisibility chain, and are unique with those profiles. -/
def xi_time_part62de_smith_profile_global_realization_statement
    (D : xi_time_part62de_smith_profile_global_realization_data) : Prop :=
  (∀ i j : Fin D.rank, i ≤ j →
      xi_time_part62de_smith_profile_global_realization_diagonalEntry D i ∣
        xi_time_part62de_smith_profile_global_realization_diagonalEntry D j) ∧
    (∀ p i,
      (xi_time_part62de_smith_profile_global_realization_diagonalEntry D i).factorization p =
        D.localExponent p i) ∧
    (∀ entries : Fin D.rank → ℕ,
      (∀ i, entries i ≠ 0) →
        (∀ p i, (entries i).factorization p = D.localExponent p i) →
          entries = xi_time_part62de_smith_profile_global_realization_diagonalEntry D)

private lemma xi_time_part62de_smith_profile_global_realization_profile_support_prime
    (D : xi_time_part62de_smith_profile_global_realization_data) (i : Fin D.rank) :
    ∀ p ∈ (xi_time_part62de_smith_profile_global_realization_profile D i).support,
      Nat.Prime p := by
  intro p hp
  exact D.support_prime p (Finsupp.support_onFinset_subset hp)

private lemma xi_time_part62de_smith_profile_global_realization_factorization
    (D : xi_time_part62de_smith_profile_global_realization_data) (i : Fin D.rank) :
    (xi_time_part62de_smith_profile_global_realization_diagonalEntry D i).factorization =
      xi_time_part62de_smith_profile_global_realization_profile D i := by
  exact Nat.prod_pow_factorization_eq_self
    (xi_time_part62de_smith_profile_global_realization_profile_support_prime D i)

private lemma xi_time_part62de_smith_profile_global_realization_factorization_apply
    (D : xi_time_part62de_smith_profile_global_realization_data) (p : ℕ) (i : Fin D.rank) :
    (xi_time_part62de_smith_profile_global_realization_diagonalEntry D i).factorization p =
      D.localExponent p i := by
  rw [xi_time_part62de_smith_profile_global_realization_factorization]
  rfl

private lemma xi_time_part62de_smith_profile_global_realization_diagonalEntry_ne_zero
    (D : xi_time_part62de_smith_profile_global_realization_data) (i : Fin D.rank) :
    xi_time_part62de_smith_profile_global_realization_diagonalEntry D i ≠ 0 := by
  rw [xi_time_part62de_smith_profile_global_realization_diagonalEntry, Finsupp.prod]
  exact Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _
    (D.support_prime p (Finsupp.support_onFinset_subset hp)).ne_zero

/-- Paper label: `thm:xi-time-part62de-smith-profile-global-realization`. -/
theorem paper_xi_time_part62de_smith_profile_global_realization
    (D : xi_time_part62de_smith_profile_global_realization_data) :
    xi_time_part62de_smith_profile_global_realization_statement D := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    apply (Nat.factorization_le_iff_dvd
      (xi_time_part62de_smith_profile_global_realization_diagonalEntry_ne_zero D i)
      (xi_time_part62de_smith_profile_global_realization_diagonalEntry_ne_zero D j)).mp
    intro p
    rw [xi_time_part62de_smith_profile_global_realization_factorization_apply,
      xi_time_part62de_smith_profile_global_realization_factorization_apply]
    exact D.monotone p i j hij
  · exact xi_time_part62de_smith_profile_global_realization_factorization_apply D
  · intro entries hentries_ne hentries_profile
    funext i
    apply Nat.eq_of_factorization_eq (hentries_ne i)
      (xi_time_part62de_smith_profile_global_realization_diagonalEntry_ne_zero D i)
    intro p
    rw [hentries_profile p i,
      xi_time_part62de_smith_profile_global_realization_factorization_apply]

end Omega.Zeta
