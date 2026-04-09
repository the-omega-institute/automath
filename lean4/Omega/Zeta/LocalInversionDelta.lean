import Mathlib.Tactic

namespace Omega.Zeta.LocalInversionDelta

open Finset

/-- Monotonicity: `#{f i ≥ k+1} ≤ #{f i ≥ k}`.
    prop:xi-cdim-local-inversion-delta -/
theorem filter_ge_card_mono {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℕ) (k : ℕ) :
    (S.filter (fun i => k + 1 ≤ f i)).card ≤ (S.filter (fun i => k ≤ f i)).card := by
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, by omega⟩

/-- Layer identity: `#{f i ≥ k} - #{f i ≥ k+1} = #{f i = k}`.
    prop:xi-cdim-local-inversion-delta -/
theorem filter_ge_card_sub_succ {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℕ) (k : ℕ) :
    (S.filter (fun i => k ≤ f i)).card - (S.filter (fun i => k + 1 ≤ f i)).card =
      (S.filter (fun i => f i = k)).card := by
  have hunion : S.filter (fun i => k ≤ f i) =
      S.filter (fun i => f i = k) ∪ S.filter (fun i => k + 1 ≤ f i) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hs, hle⟩
      rcases eq_or_lt_of_le hle with heq | hlt
      · exact Or.inl ⟨hs, heq.symm⟩
      · exact Or.inr ⟨hs, hlt⟩
    · rintro (⟨hs, heq⟩ | ⟨hs, hle⟩)
      · exact ⟨hs, by omega⟩
      · exact ⟨hs, by omega⟩
  have hdisj : Disjoint (S.filter (fun i => f i = k))
      (S.filter (fun i => k + 1 ≤ f i)) := by
    rw [Finset.disjoint_filter]
    intro i _ heq hle
    omega
  rw [hunion, Finset.card_union_of_disjoint hdisj]
  omega

/-- Paper package: local inversion delta.
    prop:xi-cdim-local-inversion-delta -/
theorem paper_xi_cdim_local_inversion_delta {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℕ) (k : ℕ) :
    (S.filter (fun i => k ≤ f i)).card - (S.filter (fun i => k + 1 ≤ f i)).card =
      (S.filter (fun i => f i = k)).card :=
  filter_ge_card_sub_succ S f k

end Omega.Zeta.LocalInversionDelta
