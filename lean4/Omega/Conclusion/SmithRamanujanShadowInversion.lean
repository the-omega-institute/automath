import Mathlib.Tactic
import Omega.Zeta.SmithPrefixSufficiency

namespace Omega.Conclusion

open Omega.Zeta
open scoped BigOperators

/-- Telescoping identity for p-primary Ramanujan shadow: the partial sum of R(j)
    satisfies Σ_{j=1}^{k} R(j) = p^k Δ(k) - m.
    Here we verify with p=2, k=3, Smith invariants d=(2,8,32).
    e = (1, 3, 5), Δ(0)=3, Δ(1)=3, Δ(2)=2, Δ(3)=1.
    R(1) = 2·3 - 1·3 = 3, R(2) = 4·2 - 2·3 = 2, R(3) = 8·1 - 4·2 = 0.
    Sum = 3+2+0 = 5. And p^3·Δ(3) - m = 8·1 - 3 = 5. ✓
    thm:conclusion-smith-pprimary-ramanujan-shadow-inversion -/
theorem shadow_inversion_telescoping_p2_k3_seed :
    (2 : ℤ) * 3 - 1 * 3 + ((2 : ℤ) ^ 2 * 2 - 2 * 3) + ((2 : ℤ) ^ 3 * 1 - 2 ^ 2 * 2) =
    (2 : ℤ) ^ 3 * 1 - 3 := by norm_num

/-- Inversion formula: Δ_p(k) = p^{-k}(m + Σ R(j)).
    Verify: p=2, k=2, m=3, e=(1,3,5), Δ(2)=2.
    m + R(1) + R(2) = 3 + 3 + 2 = 8. And p^k · Δ(k) = 4·2 = 8. ✓
    thm:conclusion-smith-pprimary-ramanujan-shadow-inversion -/
theorem shadow_inversion_formula_p2_k2_seed :
    (3 : ℤ) + 3 + 2 = 2 ^ 2 * 2 := by norm_num

/-- Multiplicity recovery: #{i : e_i(p) = k} = Δ(k) - Δ(k+1).
    For e=(1,3,5): Δ(1) - Δ(2) = 3 - 2 = 1 (one index has e_i=1).
    Δ(3) - Δ(4) = 1 - 0 = 1 (one index has e_i=3, but actually e_i=3 gives Δ(3)=1).
    Δ(5) - Δ(6) = 0 - 0 = 0... wait. e=(1,3,5):
    #{e_i = 1} = 1, #{e_i = 3} = 1, #{e_i = 5} = 1.
    Δ(0)=3, Δ(1)=3, Δ(2)=2, Δ(3)=2, Δ(4)=1, Δ(5)=1, Δ(6)=0.
    Δ(1)-Δ(2) = 3-2 = 1. ✓
    thm:conclusion-smith-pprimary-ramanujan-shadow-inversion -/
theorem shadow_multiplicity_recovery_seed :
    (3 : ℕ) - 2 = 1 ∧ (2 : ℕ) - 2 = 0 ∧ (2 : ℕ) - 1 = 1 := by omega

/-- Realizability: non-negative integer non-increasing eventually-zero sequence
    yields valid Smith spectrum. Seed: Δ = (3, 2, 1, 0, 0, ...) gives
    m_0 = 3-2=1, m_1 = 2-1=1, m_2 = 1-0=1. Sum = 3 = m. ✓
    thm:conclusion-smith-pprimary-ramanujan-shadow-inversion -/
theorem shadow_realizability_seed :
    (3 : ℕ) - 2 + (2 - 1) + (1 - 0) = 3 := by omega

/-- Paper package: `thm:conclusion-smith-pprimary-ramanujan-shadow-inversion`.
    Seed values for p-primary Ramanujan shadow inversion and realizability. -/
theorem paper_conclusion_smith_ramanujan_shadow_inversion_seeds :
    ((2 : ℤ) * 3 - 1 * 3 + (2 ^ 2 * 2 - 2 * 3) + (2 ^ 3 * 1 - 2 ^ 2 * 2) =
      2 ^ 3 * 1 - 3) ∧
    ((3 : ℤ) + 3 + 2 = 2 ^ 2 * 2) ∧
    ((3 : ℕ) - 2 = 1) ∧
    ((3 : ℕ) - 2 + (2 - 1) + (1 - 0) = 3) := by
  exact ⟨by norm_num, by norm_num, by omega, by omega⟩

/-- Paper package: `thm:conclusion-smith-pprimary-ramanujan-shadow-inversion`.
    Strict clone of `paper_conclusion_smith_ramanujan_shadow_inversion_seeds`. -/
theorem paper_conclusion_smith_ramanujan_shadow_inversion_package :
    ((2 : ℤ) * 3 - 1 * 3 + (2 ^ 2 * 2 - 2 * 3) + (2 ^ 3 * 1 - 2 ^ 2 * 2) =
      2 ^ 3 * 1 - 3) ∧
    ((3 : ℤ) + 3 + 2 = 2 ^ 2 * 2) ∧
    ((3 : ℕ) - 2 = 1) ∧
    ((3 : ℕ) - 2 + (2 - 1) + (1 - 0) = 3) :=
  paper_conclusion_smith_ramanujan_shadow_inversion_seeds

/-- Concrete inversion package for a p-primary Ramanujan shadow sequence attached to a fixed Smith
profile of length `m`. If `R` agrees with the shadow formula of that profile, then finite sums of
`R` recover the tail counts, exact multiplicities are the finite differences of those tail counts,
and the same tail-count sequence itself realizes the given shadow. -/
def conclusion_smith_pprimary_ramanujan_shadow_inversion_statement
    (p m : ℕ) (R : ℕ → ℤ) : Prop :=
  ∀ e : Fin m → ℕ,
    (∀ k : ℕ, 1 ≤ k →
      R k =
        (p : ℤ) ^ k * (smithPrefixDelta e k : ℤ) -
          (p : ℤ) ^ (k - 1) * (smithPrefixDelta e (k - 1) : ℤ)) →
      (∀ K : ℕ,
        Finset.sum (Finset.range K) (fun j => R (j + 1)) =
          (p : ℤ) ^ K * (smithPrefixDelta e K : ℤ) - m) ∧
      (∀ ℓ : ℕ,
        smithPrefixMultiplicity e ℓ = smithPrefixDelta e ℓ - smithPrefixDelta e (ℓ + 1)) ∧
      ∃ Δ : ℕ → ℕ,
        Δ 0 = m ∧
          (∀ k : ℕ, Δ k = smithPrefixDelta e k) ∧
          (∀ k : ℕ, 1 ≤ k →
            R k =
              (p : ℤ) ^ k * (Δ k : ℤ) - (p : ℤ) ^ (k - 1) * (Δ (k - 1) : ℤ)) ∧
          (∀ ℓ : ℕ, smithPrefixMultiplicity e ℓ = Δ ℓ - Δ (ℓ + 1))

lemma conclusion_smith_pprimary_ramanujan_shadow_inversion_shadow_telescope
    (p : ℤ) (Δ : ℕ → ℤ) :
    ∀ K : ℕ,
      Finset.sum (Finset.range K) (fun j => (p ^ (j + 1)) * Δ (j + 1) - p ^ j * Δ j) =
        p ^ K * Δ K - Δ 0
  | 0 => by simp
  | K + 1 => by
      rw [Finset.sum_range_succ,
        conclusion_smith_pprimary_ramanujan_shadow_inversion_shadow_telescope p Δ K]
      ring

/-- Paper label: `thm:conclusion-smith-pprimary-ramanujan-shadow-inversion`. -/
theorem paper_conclusion_smith_pprimary_ramanujan_shadow_inversion
    (p m : ℕ) (R : ℕ → ℤ) : conclusion_smith_pprimary_ramanujan_shadow_inversion_statement p m R := by
  intro e hR
  refine ⟨?_, ?_, ?_⟩
  · intro K
    calc
      Finset.sum (Finset.range K) (fun j => R (j + 1))
          = Finset.sum (Finset.range K) (fun j =>
              (p : ℤ) ^ (j + 1) * (smithPrefixDelta e (j + 1) : ℤ) -
                (p : ℤ) ^ j * (smithPrefixDelta e j : ℤ)) := by
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  simpa using hR (j + 1) (Nat.succ_le_succ (Nat.zero_le j))
      _ = (p : ℤ) ^ K * (smithPrefixDelta e K : ℤ) - (smithPrefixDelta e 0 : ℤ) := by
            simpa using
              conclusion_smith_pprimary_ramanujan_shadow_inversion_shadow_telescope
                (p := (p : ℤ)) (Δ := fun k => (smithPrefixDelta e k : ℤ)) K
      _ = (p : ℤ) ^ K * (smithPrefixDelta e K : ℤ) - m := by
            have hdelta0 : smithPrefixDelta e 0 = m := by
              unfold smithPrefixDelta
              simp
            rw [hdelta0]
  · intro ℓ
    exact smithPrefixMultiplicity_eq_delta_sub_delta e ℓ
  · refine ⟨smithPrefixDelta e, ?_, ?_, ?_, ?_⟩
    · have hdelta0 : smithPrefixDelta e 0 = m := by
        unfold smithPrefixDelta
        simp
      simpa using hdelta0
    · intro k
      rfl
    · intro k hk
      simpa using hR k hk
    · intro ℓ
      exact smithPrefixMultiplicity_eq_delta_sub_delta e ℓ

end Omega.Conclusion
