import Mathlib.Tactic
import Omega.Zeta.SmithPrefixSufficiency

namespace Omega.Zeta

private lemma smithPrefixDelta_antitone {m : ℕ} (e : Fin m → ℕ) (k : ℕ) :
    smithPrefixDelta e (k + 1) ≤ smithPrefixDelta e k := by
  unfold smithPrefixDelta
  refine Finset.sum_le_sum ?_
  intro i _
  by_cases hnext : k + 1 ≤ e i
  · have hcurr : k ≤ e i := le_trans (Nat.le_succ k) hnext
    simp [hnext, hcurr]
  · by_cases hcurr : k ≤ e i <;> simp [hnext, hcurr]

/-- Paper label: `thm:conclusion-smith-pkernel-ratio-staircase-jump-inversion`. -/
theorem paper_conclusion_smith_pkernel_ratio_staircase_jump_inversion {m : ℕ} (p : ℕ)
    (hp : 1 < p) (e : Fin m → ℕ) :
    let R : ℕ → ℕ := fun k => p ^ smithPrefixDelta e (k + 1)
    (∀ k : ℕ, R (k + 1) ∣ R k) ∧
      (∀ k : ℕ, smithPrefixTop e ≤ k → R k = 1) ∧
      (∀ ℓ : ℕ, 1 ≤ ℓ → R (ℓ - 1) = p ^ smithPrefixMultiplicity e ℓ * R ℓ) := by
  dsimp
  have _ := hp
  refine ⟨?_, ?_, ?_⟩
  · intro k
    exact pow_dvd_pow p (smithPrefixDelta_antitone e (k + 1))
  · intro k hk
    have hk' : smithPrefixTop e ≤ k + 1 := le_trans hk (Nat.le_succ k)
    have hdelta : smithPrefixDelta e (k + 1) = 0 := by
      rw [smithPrefixDelta_eq_sub, smithPrefixValue_eq_total_of_le_top e (k + 1) hk',
        smithPrefixValue_eq_total_of_le_top e k hk]
      simp
    simp [hdelta]
  · intro ℓ hℓ
    have hmono : smithPrefixDelta e (ℓ + 1) ≤ smithPrefixDelta e ℓ :=
      smithPrefixDelta_antitone e ℓ
    have hpow :
        p ^ smithPrefixDelta e ℓ =
          p ^ smithPrefixMultiplicity e ℓ * p ^ smithPrefixDelta e (ℓ + 1) := by
      rw [smithPrefixMultiplicity_eq_delta_sub_delta, ← Nat.pow_add, Nat.sub_add_cancel hmono]
    simpa [Nat.sub_add_cancel hℓ] using hpow

end Omega.Zeta
