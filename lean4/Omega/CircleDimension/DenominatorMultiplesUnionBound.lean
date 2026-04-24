import Mathlib.Tactic
import Mathlib.Data.Nat.Factorization.Basic

namespace Omega.CircleDimension.DenominatorMultiplesUnionBound

open Finset

/-- Multiples of `q` in the interval `[1, B]`.
    prop:cdim-denominator-positive-density-thin-forbidden -/
def multiplesUpTo (q B : ℕ) : Finset ℕ :=
  (Finset.Icc 1 B).filter (fun n => q ∣ n)

/-- Cardinality of multiples of `q` in `[1, B]` is `⌊B/q⌋`.
    prop:cdim-denominator-positive-density-thin-forbidden -/
theorem card_multiplesUpTo (q B : ℕ) : (multiplesUpTo q B).card = B / q := by
  unfold multiplesUpTo
  have hIcc : (Finset.Icc 1 B) = Finset.Ioc 0 B := by
    ext n; simp [Nat.lt_iff_add_one_le]
  rw [hIcc]
  exact Nat.Ioc_filter_dvd_card_eq_div B q

/-- Forbidden multiples: union of multiples of all `q ∈ Q` in `[1, B]`.
    prop:cdim-denominator-positive-density-thin-forbidden -/
def forbiddenMultiples (Q : Finset ℕ) (B : ℕ) : Finset ℕ :=
  Q.biUnion (fun q => multiplesUpTo q B)

/-- `forbiddenMultiples` equals the filtered `[1, B]` by "has some divisor in `Q`".
    prop:cdim-denominator-positive-density-thin-forbidden -/
theorem forbiddenMultiples_eq_filter (Q : Finset ℕ) (B : ℕ) :
    forbiddenMultiples Q B =
      (Finset.Icc 1 B).filter (fun n => ∃ q ∈ Q, q ∣ n) := by
  unfold forbiddenMultiples multiplesUpTo
  ext n
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨q, hqQ, hIcc, hdvd⟩
    exact ⟨hIcc, q, hqQ, hdvd⟩
  · rintro ⟨hIcc, q, hqQ, hdvd⟩
    exact ⟨q, hqQ, hIcc, hdvd⟩

/-- Union bound: `|forbiddenMultiples Q B| ≤ ∑_{q ∈ Q} ⌊B/q⌋`.
    prop:cdim-denominator-positive-density-thin-forbidden -/
theorem card_forbiddenMultiples_le_sum (Q : Finset ℕ) (B : ℕ) :
    (forbiddenMultiples Q B).card ≤ ∑ q ∈ Q, B / q := by
  unfold forbiddenMultiples
  have h1 : (Q.biUnion (fun q => multiplesUpTo q B)).card ≤
      ∑ q ∈ Q, (multiplesUpTo q B).card :=
    Finset.card_biUnion_le
  have h2 : (∑ q ∈ Q, (multiplesUpTo q B).card) = ∑ q ∈ Q, B / q :=
    Finset.sum_congr rfl (fun q _ => card_multiplesUpTo q B)
  linarith [h1, h2 ▸ h1]

/-- Lower bound on the count of "no divisor in `Q`" elements.
    prop:cdim-denominator-positive-density-thin-forbidden -/
theorem card_non_multiples_ge (Q : Finset ℕ) (B : ℕ) :
    ((Finset.Icc 1 B).filter (fun n => ∀ q ∈ Q, ¬ q ∣ n)).card ≥
      B - ∑ q ∈ Q, B / q := by
  have hforbid_subset : forbiddenMultiples Q B ⊆ Finset.Icc 1 B := by
    intro n hn
    rw [forbiddenMultiples_eq_filter] at hn
    exact (Finset.mem_filter.mp hn).1
  have hIcc_card : (Finset.Icc 1 B).card = B := by
    rw [Nat.card_Icc]; omega
  -- complement of forbidden in Icc 1 B is exactly "∀ q ∈ Q, ¬ q ∣ n"
  have hcompl : ((Finset.Icc 1 B).filter (fun n => ∀ q ∈ Q, ¬ q ∣ n)) =
      (Finset.Icc 1 B) \ forbiddenMultiples Q B := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_Icc,
      forbiddenMultiples_eq_filter]
    constructor
    · rintro ⟨hIcc, hnone⟩
      refine ⟨hIcc, ?_⟩
      rintro ⟨_, q, hqQ, hdvd⟩
      exact hnone q hqQ hdvd
    · rintro ⟨hIcc, hnot⟩
      refine ⟨hIcc, ?_⟩
      intro q hqQ hdvd
      exact hnot ⟨hIcc, q, hqQ, hdvd⟩
  rw [hcompl]
  have hcard : ((Finset.Icc 1 B) \ forbiddenMultiples Q B).card =
      (Finset.Icc 1 B).card - (forbiddenMultiples Q B).card :=
    Finset.card_sdiff_of_subset hforbid_subset
  rw [hcard, hIcc_card]
  have hbnd := card_forbiddenMultiples_le_sum Q B
  omega

/-- Paper package: denominator positive density — forbidden upper bound.
    prop:cdim-denominator-positive-density-thin-forbidden -/
theorem paper_cdim_denominator_positive_density_forbidden_upper
    (Q : Finset ℕ) (B : ℕ) :
    (forbiddenMultiples Q B).card ≤ ∑ q ∈ Q, B / q :=
  card_forbiddenMultiples_le_sum Q B

/-- Seed: |multiples of 2 in [1,100]| = 50.
    prop:cdim-denominator-positive-density-thin-forbidden -/
theorem card_multiplesUpTo_2_100 : (multiplesUpTo 2 100).card = 50 := by
  rw [card_multiplesUpTo]

/-- Seed: |multiples of 3 in [1,100]| = 33.
    prop:cdim-denominator-positive-density-thin-forbidden -/
theorem card_multiplesUpTo_3_100 : (multiplesUpTo 3 100).card = 33 := by
  rw [card_multiplesUpTo]

/-- Seed: |multiples of 5 in [1,100]| = 20.
    prop:cdim-denominator-positive-density-thin-forbidden -/
theorem card_multiplesUpTo_5_100 : (multiplesUpTo 5 100).card = 20 := by
  rw [card_multiplesUpTo]

/-- Seed: |multiples of 6 in [1,100]| = 16.
    prop:cdim-denominator-positive-density-thin-forbidden -/
theorem card_multiplesUpTo_6_100 : (multiplesUpTo 6 100).card = 16 := by
  rw [card_multiplesUpTo]

/-- Union bound seed: for Q={2,3,5}, |forbidden in [1,100]| ≤ 50+33+20 = 103.
    prop:cdim-denominator-positive-density-thin-forbidden -/
theorem card_forbiddenMultiples_235_100 :
    (forbiddenMultiples {2, 3, 5} 100).card ≤ 103 := by
  have h := card_forbiddenMultiples_le_sum {2, 3, 5} 100
  simp only [Finset.sum_insert (by decide : (2 : ℕ) ∉ ({3, 5} : Finset ℕ)),
    Finset.sum_insert (by decide : (3 : ℕ) ∉ ({5} : Finset ℕ)),
    Finset.sum_singleton] at h
  omega

/-- Non-multiples lower bound seed: for Q={2,3,5}, B=100, at least 100-103 elements survive
    (trivially ≥ 0, but the actual count is higher due to inclusion-exclusion).
    prop:cdim-denominator-positive-density-thin-forbidden -/
theorem card_non_multiples_235_100 :
    ((Finset.Icc 1 100).filter (fun n => ∀ q ∈ ({2, 3, 5} : Finset ℕ), ¬ q ∣ n)).card ≥ 0 := by
  omega

/-- Paper package: denominator multiples union bound with concrete seeds.
    prop:cdim-denominator-positive-density-thin-forbidden -/
theorem paper_cdim_denominator_multiples_seeds :
    (multiplesUpTo 2 100).card = 50 ∧
    (multiplesUpTo 3 100).card = 33 ∧
    (multiplesUpTo 5 100).card = 20 ∧
    (multiplesUpTo 6 100).card = 16 ∧
    (forbiddenMultiples {2, 3, 5} 100).card ≤ 103 :=
  ⟨card_multiplesUpTo_2_100, card_multiplesUpTo_3_100,
   card_multiplesUpTo_5_100, card_multiplesUpTo_6_100,
   card_forbiddenMultiples_235_100⟩

/-- Exact finite witness: among `1..100`, exactly `26` integers avoid divisibility by `2`, `3`,
and `5`.
    prop:cdim-denominator-positive-density-thin-forbidden -/
theorem card_non_multiples_235_100_exact :
    ((Finset.Icc 1 100).filter (fun n => ∀ q ∈ ({2, 3, 5} : Finset ℕ), ¬ q ∣ n)).card = 26 := by
  native_decide

/-- Paper-facing denominator-thinness package: the forbidden union is controlled by the finite
union bound, the complement count has the corresponding lower bound, and the concrete truncation
`Q = {2,3,5}` still leaves a positive surviving set in `[1,100]`.
    prop:cdim-denominator-positive-density-thin-forbidden -/
theorem paper_cdim_denominator_positive_density_thin_forbidden :
    (∀ (Q : Finset ℕ) (B : ℕ), (forbiddenMultiples Q B).card ≤ ∑ q ∈ Q, B / q) ∧
    (∀ (Q : Finset ℕ) (B : ℕ),
      ((Finset.Icc 1 B).filter (fun n => ∀ q ∈ Q, ¬ q ∣ n)).card ≥ B - ∑ q ∈ Q, B / q) ∧
    (((Finset.Icc 1 100).filter (fun n => ∀ q ∈ ({2, 3, 5} : Finset ℕ), ¬ q ∣ n)).card = 26) := by
  exact ⟨card_forbiddenMultiples_le_sum, card_non_multiples_ge, card_non_multiples_235_100_exact⟩

end Omega.CircleDimension.DenominatorMultiplesUnionBound
