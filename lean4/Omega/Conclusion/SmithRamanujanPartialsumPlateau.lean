import Mathlib.Tactic
import Omega.Conclusion.SmithRamanujanShadowInversion

namespace Omega.Conclusion

open Omega.Zeta
open scoped BigOperators

/-- The Ramanujan partial sum `S_p(k) = m + Σ_{j=1}^k R(j)`. -/
def conclusion_smith_ramanujan_partialsum_plateau_partial_sum
    (m : ℕ) (R : ℕ → ℤ) (k : ℕ) : ℤ :=
  (m : ℤ) + ∑ j ∈ Finset.range k, R (j + 1)

/-- Paper-facing Smith/Ramanujan partial-sum plateau package. The partial sums recover the
`p`-primary tail counts, vanish exactly after the top Smith exponent, stay positive up to that
last plateau, and the multiplicities are the finite differences of the tail counts. -/
def conclusion_smith_ramanujan_partialsum_plateau_statement : Prop :=
  ∀ {m : ℕ} (e : Fin m → ℕ) (p : ℕ) (_hp : Nat.Prime p) (R : ℕ → ℤ),
    (∀ k : ℕ, 1 ≤ k →
      R k =
        (p : ℤ) ^ k * (smithPrefixDelta e k : ℤ) -
          (p : ℤ) ^ (k - 1) * (smithPrefixDelta e (k - 1) : ℤ)) →
      (∀ k : ℕ,
        conclusion_smith_ramanujan_partialsum_plateau_partial_sum m R k =
          (p : ℤ) ^ k * (smithPrefixDelta e k : ℤ)) ∧
      conclusion_smith_ramanujan_partialsum_plateau_partial_sum m R (smithPrefixTop e + 1) = 0 ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ smithPrefixTop e →
        0 < conclusion_smith_ramanujan_partialsum_plateau_partial_sum m R k) ∧
      (∀ ℓ : ℕ, smithPrefixMultiplicity e ℓ = smithPrefixDelta e ℓ - smithPrefixDelta e (ℓ + 1))

/-- Paper label: `thm:conclusion-smith-ramanujan-partialsum-plateau`. -/
def paper_conclusion_smith_ramanujan_partialsum_plateau : Prop :=
  conclusion_smith_ramanujan_partialsum_plateau_statement

theorem conclusion_smith_ramanujan_partialsum_plateau_verified :
    paper_conclusion_smith_ramanujan_partialsum_plateau := by
  intro m e p hp R hR
  rcases paper_conclusion_smith_pprimary_ramanujan_shadow_inversion p m R e hR with
    ⟨htel, hmult, _⟩
  have hpartial :
      ∀ k : ℕ,
        conclusion_smith_ramanujan_partialsum_plateau_partial_sum m R k =
          (p : ℤ) ^ k * (smithPrefixDelta e k : ℤ) := by
    intro k
    unfold conclusion_smith_ramanujan_partialsum_plateau_partial_sum
    calc
      (m : ℤ) + ∑ j ∈ Finset.range k, R (j + 1)
          = (m : ℤ) + ((p : ℤ) ^ k * (smithPrefixDelta e k : ℤ) - m) := by
              rw [htel k]
      _ = (p : ℤ) ^ k * (smithPrefixDelta e k : ℤ) := by ring
  have hdelta_zero : smithPrefixDelta e (smithPrefixTop e + 1) = 0 := by
    rw [smithPrefixDelta_eq_sub, smithPrefix_top_plateau]
    exact Nat.sub_self _
  have hplateau :
      conclusion_smith_ramanujan_partialsum_plateau_partial_sum m R (smithPrefixTop e + 1) = 0 := by
    rw [hpartial (smithPrefixTop e + 1), hdelta_zero]
    simp
  have hpz : 0 < (p : ℤ) := by
    exact_mod_cast hp.pos
  have hpositive :
      ∀ k : ℕ, 1 ≤ k → k ≤ smithPrefixTop e →
        0 < conclusion_smith_ramanujan_partialsum_plateau_partial_sum m R k := by
    intro k hk1 hkE
    have hdelta_pos : 0 < smithPrefixDelta e k := smithPrefixDelta_pos_of_le_top e hk1 hkE
    have hpow_pos : 0 < (p : ℤ) ^ k := pow_pos hpz _
    calc
      0 < (p : ℤ) ^ k * (smithPrefixDelta e k : ℤ) := by
            exact mul_pos hpow_pos (by exact_mod_cast hdelta_pos)
      _ = conclusion_smith_ramanujan_partialsum_plateau_partial_sum m R k := by
            symm
            exact hpartial k
  exact ⟨hpartial, hplateau, hpositive, hmult⟩

end Omega.Conclusion
