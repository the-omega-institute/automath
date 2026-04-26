import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite-channel negative-inertia ledger.  The channel family is finite, `k_chi`
records the negative-inertia count of a scalar channel, and `K` is the total block negative
inertia supplied by the direct-sum decomposition. -/
structure xi_abelian_visible_channel_negative_support_incompressible_data where
  channelCount : ℕ
  N : ℕ
  k_chi : Fin channelCount → ℕ
  K : ℕ
  K_eq_sum : K = Finset.univ.sum k_chi
  channel_bound : ∀ chi : Fin channelCount, k_chi chi ≤ N + 1

namespace xi_abelian_visible_channel_negative_support_incompressible_data

/-- The finite support of channels that carry at least one negative direction. -/
def xi_abelian_visible_channel_negative_support_incompressible_support
    (D : xi_abelian_visible_channel_negative_support_incompressible_data) :
    Finset (Fin D.channelCount) :=
  Finset.univ.filter fun chi => 1 ≤ D.k_chi chi

/-- Paper-facing statement: the total count is bounded by `(N+1)` times the visible negative
support, while every supported channel contributes at least one unit to the total. -/
def xi_abelian_visible_channel_negative_support_incompressible_statement
    (D : xi_abelian_visible_channel_negative_support_incompressible_data) : Prop :=
  D.K ≤ (D.N + 1) *
      (D.xi_abelian_visible_channel_negative_support_incompressible_support.card) ∧
    D.xi_abelian_visible_channel_negative_support_incompressible_support.card ≤ D.K

end xi_abelian_visible_channel_negative_support_incompressible_data

open xi_abelian_visible_channel_negative_support_incompressible_data

/-- Paper label: `thm:xi-abelian-visible-channel-negative-support-incompressible`.

Summing the channel negative-inertia counts over the finite support gives the two elementary
support inequalities. -/
theorem paper_xi_abelian_visible_channel_negative_support_incompressible
    (D : xi_abelian_visible_channel_negative_support_incompressible_data) :
    xi_abelian_visible_channel_negative_support_incompressible_statement D := by
  let S := D.xi_abelian_visible_channel_negative_support_incompressible_support
  have hSupport :
      ∀ chi : Fin D.channelCount, chi ∈ S ↔ 1 ≤ D.k_chi chi := by
    intro chi
    simp [S, xi_abelian_visible_channel_negative_support_incompressible_support]
  have hK_sum_support : D.K = S.sum D.k_chi := by
    rw [D.K_eq_sum]
    symm
    refine Finset.sum_subset ?_ ?_
    · intro chi hchi
      simp
    · intro chi _ hchiS
      have hnot : ¬ 1 ≤ D.k_chi chi := by
        exact fun hle => hchiS ((hSupport chi).2 hle)
      exact Nat.eq_zero_of_not_pos hnot
  have hUpperSum : S.sum D.k_chi ≤ S.sum fun _ : Fin D.channelCount => D.N + 1 := by
    exact Finset.sum_le_sum fun chi _ => D.channel_bound chi
  have hUpper : D.K ≤ (D.N + 1) * S.card := by
    rw [hK_sum_support]
    refine hUpperSum.trans_eq ?_
    simp [Finset.sum_const, mul_comm]
  have hLowerSum : S.sum (fun _ : Fin D.channelCount => 1) ≤ S.sum D.k_chi := by
    exact Finset.sum_le_sum fun chi hchi => (hSupport chi).1 hchi
  have hLower : S.card ≤ D.K := by
    rw [hK_sum_support]
    simpa using hLowerSum
  exact ⟨hUpper, hLower⟩

end Omega.Zeta
