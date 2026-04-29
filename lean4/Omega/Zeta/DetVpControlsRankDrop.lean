import Mathlib.Tactic
import Omega.Zeta.SmithPrefixSufficiency

namespace Omega.Zeta

open scoped BigOperators

/-- The mod-`p` rank drop attached to a Smith diagonal is the number of positive `p`-exponents. -/
def xiDetRankDropAtPrime {m : ℕ} (_p : ℕ) (e : Fin m → ℕ) : ℕ :=
  smithPrefixDelta e 1

/-- The `p`-adic valuation of the determinant is the sum of the Smith exponents. -/
def xiDetValuationAtPrime {m : ℕ} (_p : ℕ) (e : Fin m → ℕ) : ℕ :=
  ∑ i, e i

lemma xiDetRankDropAtPrime_le_detValuationAtPrime {m : ℕ} (p : ℕ) (e : Fin m → ℕ) :
    xiDetRankDropAtPrime p e ≤ xiDetValuationAtPrime p e := by
  unfold xiDetRankDropAtPrime xiDetValuationAtPrime smithPrefixDelta
  refine Finset.sum_le_sum ?_
  intro i _
  by_cases hi : 1 ≤ e i
  · simp [hi]
  · simp [hi]

lemma xiDetRankDropAtPrime_eq_zero_of_detValuationAtPrime_eq_zero
    {m : ℕ} (p : ℕ) (e : Fin m → ℕ) (hdet : xiDetValuationAtPrime p e = 0) :
    xiDetRankDropAtPrime p e = 0 := by
  apply le_antisymm
  · calc
      xiDetRankDropAtPrime p e ≤ xiDetValuationAtPrime p e :=
        xiDetRankDropAtPrime_le_detValuationAtPrime p e
      _ = 0 := hdet
  · exact Nat.zero_le _

/-- In Smith normal form, the mod-`p` rank drop is the number of diagonal entries divisible by
`p`, hence it is bounded by the sum of their `p`-adic exponents. If the determinant valuation
vanishes, the reduction mod `p` stays full rank.
    prop:xi-det-vp-controls-rank-drop -/
theorem paper_xi_det_vp_controls_rank_drop {m : ℕ} (e : Fin m → ℕ) :
    (∀ p, Nat.Prime p → xiDetRankDropAtPrime p e ≤ xiDetValuationAtPrime p e) ∧
      (∀ p, Nat.Prime p → xiDetValuationAtPrime p e = 0 → xiDetRankDropAtPrime p e = 0) := by
  refine ⟨?_, ?_⟩
  · intro p _hp
    exact xiDetRankDropAtPrime_le_detValuationAtPrime p e
  · intro p _hp hdet
    exact xiDetRankDropAtPrime_eq_zero_of_detValuationAtPrime_eq_zero p e hdet

end Omega.Zeta
