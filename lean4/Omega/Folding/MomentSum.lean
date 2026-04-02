import Omega.Folding.MaxFiber
import Mathlib.Algebra.Order.Chebyshev

namespace Omega

/-- S_q(m) = Σ_{x : X m} d_m(x)^q, the q-th moment of the fiber multiplicity distribution.
    subsec:op_algebra_complexity-momentSum -/
noncomputable def momentSum (q m : Nat) : Nat :=
  ∑ x : X m, (X.fiberMultiplicity x) ^ q

/-- S_0(m) = |X_m| = F(m+1).
    subsec:op_algebra_complexity-momentSum-zero -/
theorem momentSum_zero (m : Nat) : momentSum 0 m = Nat.fib (m + 2) := by
  simp only [momentSum, pow_zero, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
    X.card_eq_fib]

/-- S_1(m) = 2^m (fiber multiplicities sum to the word count).
    subsec:op_algebra_complexity-momentSum-one -/
theorem momentSum_one (m : Nat) : momentSum 1 m = 2 ^ m := by
  simp only [momentSum, pow_one, X.fiberMultiplicity_sum_eq_pow]

/-- S_q(m) ≤ D_m^(q-1) * 2^m: the q-th moment is bounded by the max multiplicity.
    subsec:op_algebra_complexity-momentSum-le-max-pow -/
theorem momentSum_le_max_pow (q m : Nat) (hq : 1 ≤ q) :
    momentSum q m ≤ (X.maxFiberMultiplicity m) ^ (q - 1) * 2 ^ m := by
  simp only [momentSum]
  calc ∑ x : X m, (X.fiberMultiplicity x) ^ q
      = ∑ x : X m, (X.fiberMultiplicity x) ^ (q - 1) * (X.fiberMultiplicity x) ^ 1 := by
        congr 1; ext x; rw [← pow_add]; congr 1; omega
    _ = ∑ x : X m, (X.fiberMultiplicity x) ^ (q - 1) * X.fiberMultiplicity x := by
        simp only [pow_one]
    _ ≤ ∑ x : X m, (X.maxFiberMultiplicity m) ^ (q - 1) * X.fiberMultiplicity x := by
        apply Finset.sum_le_sum; intro x _
        apply Nat.mul_le_mul_right
        exact Nat.pow_le_pow_left (X.fiberMultiplicity_le_max x) (q - 1)
    _ = (X.maxFiberMultiplicity m) ^ (q - 1) * ∑ x : X m, X.fiberMultiplicity x := by
        rw [Finset.mul_sum]
    _ = (X.maxFiberMultiplicity m) ^ (q - 1) * 2 ^ m := by
        rw [X.fiberMultiplicity_sum_eq_pow]

section Computable

/-- Computable version of momentSum using the decidable infrastructure from MaxFiber.
    prop:pom-s2-recurrence-cMomentSum -/
def cMomentSum (q m : Nat) : Nat :=
  (@Finset.univ (X m) (fintypeX m)).sum (fun x => (cFiberMult x) ^ q)

/-- prop:pom-s2-recurrence-cMomentSum-eq -/
theorem cMomentSum_eq (q m : Nat) : cMomentSum q m = momentSum q m := by
  simp only [cMomentSum, momentSum]
  apply Finset.sum_equiv (Equiv.refl _) (by simp) (fun x _ => by simp [cFiberMult_eq])

end Computable

-- Cached @[simp] lemmas for cMomentSum base values
-- S_2
@[simp] theorem cached_cMomentSum_2_0 : cMomentSum 2 0 = 1 := by native_decide
@[simp] theorem cached_cMomentSum_2_1 : cMomentSum 2 1 = 2 := by native_decide
@[simp] theorem cached_cMomentSum_2_2 : cMomentSum 2 2 = 6 := by native_decide
@[simp] theorem cached_cMomentSum_2_3 : cMomentSum 2 3 = 14 := by native_decide
@[simp] theorem cached_cMomentSum_2_4 : cMomentSum 2 4 = 36 := by native_decide
@[simp] theorem cached_cMomentSum_2_5 : cMomentSum 2 5 = 88 := by native_decide
@[simp] theorem cached_cMomentSum_2_6 : cMomentSum 2 6 = 220 := by native_decide
@[simp] theorem cached_cMomentSum_2_7 : cMomentSum 2 7 = 544 := by native_decide
-- S_3
@[simp] theorem cached_cMomentSum_3_0 : cMomentSum 3 0 = 1 := by native_decide
@[simp] theorem cached_cMomentSum_3_1 : cMomentSum 3 1 = 2 := by native_decide
@[simp] theorem cached_cMomentSum_3_2 : cMomentSum 3 2 = 10 := by native_decide
@[simp] theorem cached_cMomentSum_3_3 : cMomentSum 3 3 = 26 := by native_decide
@[simp] theorem cached_cMomentSum_3_4 : cMomentSum 3 4 = 88 := by native_decide
@[simp] theorem cached_cMomentSum_3_5 : cMomentSum 3 5 = 260 := by native_decide
@[simp] theorem cached_cMomentSum_3_6 : cMomentSum 3 6 = 820 := by native_decide
@[simp] theorem cached_cMomentSum_3_7 : cMomentSum 3 7 = 2504 := by native_decide
-- S_4
@[simp] theorem cached_cMomentSum_4_0 : cMomentSum 4 0 = 1 := by native_decide
@[simp] theorem cached_cMomentSum_4_1 : cMomentSum 4 1 = 2 := by native_decide
@[simp] theorem cached_cMomentSum_4_2 : cMomentSum 4 2 = 18 := by native_decide
@[simp] theorem cached_cMomentSum_4_3 : cMomentSum 4 3 = 50 := by native_decide
@[simp] theorem cached_cMomentSum_4_4 : cMomentSum 4 4 = 228 := by native_decide
@[simp] theorem cached_cMomentSum_4_5 : cMomentSum 4 5 = 808 := by native_decide
@[simp] theorem cached_cMomentSum_4_6 : cMomentSum 4 6 = 3244 := by native_decide
-- S_5
/-- def:pom-s5 -/
@[simp] theorem cached_cMomentSum_5_0 : cMomentSum 5 0 = 1 := by native_decide
@[simp] theorem cached_cMomentSum_5_1 : cMomentSum 5 1 = 2 := by native_decide
@[simp] theorem cached_cMomentSum_5_2 : cMomentSum 5 2 = 34 := by native_decide
@[simp] theorem cached_cMomentSum_5_3 : cMomentSum 5 3 = 98 := by native_decide
@[simp] theorem cached_cMomentSum_5_4 : cMomentSum 5 4 = 616 := by native_decide
@[simp] theorem cached_cMomentSum_5_5 : cMomentSum 5 5 = 2612 := by native_decide
-- S_6
@[simp] theorem cached_cMomentSum_6_0 : cMomentSum 6 0 = 1 := by native_decide
@[simp] theorem cached_cMomentSum_6_1 : cMomentSum 6 1 = 2 := by native_decide
@[simp] theorem cached_cMomentSum_6_2 : cMomentSum 6 2 = 66 := by native_decide
@[simp] theorem cached_cMomentSum_6_3 : cMomentSum 6 3 = 194 := by native_decide
@[simp] theorem cached_cMomentSum_6_4 : cMomentSum 6 4 = 1716 := by native_decide
-- S_7
@[simp] theorem cached_cMomentSum_7_0 : cMomentSum 7 0 = 1 := by native_decide
@[simp] theorem cached_cMomentSum_7_1 : cMomentSum 7 1 = 2 := by native_decide
@[simp] theorem cached_cMomentSum_7_2 : cMomentSum 7 2 = 130 := by native_decide
@[simp] theorem cached_cMomentSum_7_3 : cMomentSum 7 3 = 386 := by native_decide
-- S_8 (only S_2(8) needed downstream)
@[simp] theorem cached_cMomentSum_8_2 : cMomentSum 8 2 = 258 := by native_decide
-- S_9 (only S_2(9) needed downstream)
@[simp] theorem cached_cMomentSum_9_2 : cMomentSum 9 2 = 514 := by native_decide
-- S_10 (only S_2(10) needed downstream)
@[simp] theorem cached_cMomentSum_10_2 : cMomentSum 10 2 = 1026 := by native_decide

-- S_2 base values
/-- prop:pom-s2-recurrence-base-0 -/
theorem momentSum_two_zero : momentSum 2 0 = 1 := by rw [← cMomentSum_eq]; simp
/-- prop:pom-s2-recurrence-base-1 -/
theorem momentSum_two_one : momentSum 2 1 = 2 := by rw [← cMomentSum_eq]; simp
/-- prop:pom-s2-recurrence-base-2 -/
theorem momentSum_two_two : momentSum 2 2 = 6 := by rw [← cMomentSum_eq]; simp
/-- prop:pom-s2-recurrence-base-3 -/
theorem momentSum_two_three : momentSum 2 3 = 14 := by rw [← cMomentSum_eq]; simp
/-- prop:pom-s2-recurrence-base-4 -/
theorem momentSum_two_four : momentSum 2 4 = 36 := by rw [← cMomentSum_eq]; simp
/-- prop:pom-s2-recurrence-base-5 -/
theorem momentSum_two_five : momentSum 2 5 = 88 := by rw [← cMomentSum_eq]; simp
/-- prop:pom-s2-recurrence-base-6 -/
theorem momentSum_two_six : momentSum 2 6 = 220 := by rw [← cMomentSum_eq]; simp
/-- prop:pom-s2-recurrence-base-7 -/
theorem momentSum_two_seven : momentSum 2 7 = 544 := by rw [← cMomentSum_eq]; simp

-- S_3 base values
/-- prop:pom-s3-recurrence-base-0 -/
theorem momentSum_three_zero : momentSum 3 0 = 1 := by rw [← cMomentSum_eq]; simp
/-- prop:pom-s3-recurrence-base-1 -/
theorem momentSum_three_one : momentSum 3 1 = 2 := by rw [← cMomentSum_eq]; simp
/-- prop:pom-s3-recurrence-base-2 -/
theorem momentSum_three_two : momentSum 3 2 = 10 := by rw [← cMomentSum_eq]; simp
/-- prop:pom-s3-recurrence-base-3 -/
theorem momentSum_three_three : momentSum 3 3 = 26 := by rw [← cMomentSum_eq]; simp
/-- prop:pom-s3-recurrence-base-4 -/
theorem momentSum_three_four : momentSum 3 4 = 88 := by rw [← cMomentSum_eq]; simp
/-- prop:pom-s3-recurrence-base-5 -/
theorem momentSum_three_five : momentSum 3 5 = 260 := by rw [← cMomentSum_eq]; simp
/-- prop:pom-s3-recurrence-base-6 -/
theorem momentSum_three_six : momentSum 3 6 = 820 := by rw [← cMomentSum_eq]; simp
/-- prop:pom-s3-recurrence-base-7 -/
theorem momentSum_three_seven : momentSum 3 7 = 2504 := by rw [← cMomentSum_eq]; simp

-- S_4 base values via cached lemmas
/-- prop:pom-s4-base-value-0 -/
theorem momentSum_four_zero : momentSum 4 0 = 1 := by rw [← cMomentSum_eq]; simp
/-- prop:pom-s4-base-value-1 -/
theorem momentSum_four_one : momentSum 4 1 = 2 := by rw [← cMomentSum_eq]; simp
/-- prop:pom-s4-base-value-2 -/
theorem momentSum_four_two : momentSum 4 2 = 18 := by rw [← cMomentSum_eq]; simp
/-- prop:pom-s4-base-value-3 -/
theorem momentSum_four_three : momentSum 4 3 = 50 := by rw [← cMomentSum_eq]; simp
/-- prop:pom-s4-base-value-4 -/
theorem momentSum_four_four : momentSum 4 4 = 228 := by rw [← cMomentSum_eq]; simp
/-- prop:pom-s4-base-value-5 -/
theorem momentSum_four_five : momentSum 4 5 = 808 := by rw [← cMomentSum_eq]; simp
/-- prop:pom-s4-base-value-6 -/
theorem momentSum_four_six : momentSum 4 6 = 3244 := by rw [← cMomentSum_eq]; simp

-- S_5 base values
/-- prop:pom-s5-base-zero -/
theorem momentSum_five_zero : momentSum 5 0 = 1 := by rw [← cMomentSum_eq]; simp
/-- prop:pom-s5-base-one -/
theorem momentSum_five_one : momentSum 5 1 = 2 := by rw [← cMomentSum_eq]; simp
/-- prop:pom-s5-base-two -/
theorem momentSum_five_two : momentSum 5 2 = 34 := by rw [← cMomentSum_eq]; simp
/-- prop:pom-s5-base-three -/
theorem momentSum_five_three : momentSum 5 3 = 98 := by rw [← cMomentSum_eq]; simp
/-- prop:pom-s5-base-four -/
theorem momentSum_five_four : momentSum 5 4 = 616 := by rw [← cMomentSum_eq]; simp
/-- prop:pom-s5-base-five -/
theorem momentSum_five_five : momentSum 5 5 = 2612 := by rw [← cMomentSum_eq]; simp

-- S_6 base values
/-- prop:pom-s6-base-zero -/
theorem momentSum_six_zero : momentSum 6 0 = 1 := by rw [← cMomentSum_eq]; simp
/-- prop:pom-s6-base-one -/
theorem momentSum_six_one : momentSum 6 1 = 2 := by rw [← cMomentSum_eq]; simp
/-- prop:pom-s6-base-two -/
theorem momentSum_six_two : momentSum 6 2 = 66 := by rw [← cMomentSum_eq]; simp
/-- prop:pom-s6-base-three -/
theorem momentSum_six_three : momentSum 6 3 = 194 := by rw [← cMomentSum_eq]; simp
/-- prop:pom-s6-base-four -/
theorem momentSum_six_four : momentSum 6 4 = 1716 := by rw [← cMomentSum_eq]; simp

-- S_7 base values
/-- prop:pom-s7-base-zero -/
theorem momentSum_seven_zero : momentSum 7 0 = 1 := by rw [← cMomentSum_eq]; simp
/-- prop:pom-s7-base-one -/
theorem momentSum_seven_one : momentSum 7 1 = 2 := by rw [← cMomentSum_eq]; simp
/-- prop:pom-s7-base-two -/
theorem momentSum_seven_two : momentSum 7 2 = 130 := by rw [← cMomentSum_eq]; simp
/-- prop:pom-s7-base-three -/
theorem momentSum_seven_three : momentSum 7 3 = 386 := by rw [← cMomentSum_eq]; simp

-- S_8 base values (q=0,1 trivial via native_decide on X(0)/X(1), q=2 via cached)
/-- prop:pom-s8-base-zero -/
theorem momentSum_eight_zero : momentSum 8 0 = 1 := by rw [← cMomentSum_eq]; native_decide
/-- prop:pom-s8-base-one -/
theorem momentSum_eight_one : momentSum 8 1 = 2 := by rw [← cMomentSum_eq]; native_decide
/-- prop:pom-s8-base-two -/
theorem momentSum_eight_two : momentSum 8 2 = 258 := by rw [← cMomentSum_eq]; simp

-- S_9 base values
/-- prop:pom-s9-base-values-two -/
theorem momentSum_nine_two : momentSum 9 2 = 514 := by rw [← cMomentSum_eq]; simp

-- S_10 base values
/-- prop:pom-s10-base-values-two -/
theorem momentSum_ten_two : momentSum 10 2 = 1026 := by rw [← cMomentSum_eq]; simp

/-! ### Universal base values -/

/-- S_q(0) = 1 for all q: X_0 has one element with fiber multiplicity 1.
    prop:pom-moment-zero-univ -/
theorem momentSum_zero_univ (q : Nat) : momentSum q 0 = 1 := by
  simp only [momentSum]
  have hcard : Fintype.card (X 0) = 1 := by rw [X.card_eq_fib]; rfl
  have hsum : ∑ x : X 0, X.fiberMultiplicity x = 1 :=
    X.fiberMultiplicity_sum_eq_pow (m := 0)
  -- All fiber multiplicities are 1 (sum = 1 and all ≥ 1, with |X_0| = 1)
  have hall : ∀ x : X 0, X.fiberMultiplicity x = 1 := by
    intro x; have := X.fiberMultiplicity_pos x
    have : Fintype.card (X 0) = 1 := hcard
    have : ∑ y : X 0, X.fiberMultiplicity y = 1 := hsum
    have hle : X.fiberMultiplicity x ≤ 1 := by
      calc X.fiberMultiplicity x
          ≤ ∑ y : X 0, X.fiberMultiplicity y := Finset.single_le_sum
              (fun y _ => Nat.zero_le _) (Finset.mem_univ x)
        _ = 1 := hsum
    omega
  simp [hall]

/-- S_q(1) = 2 for all q: X_1 has two elements, each with fiber multiplicity 1.
    prop:pom-moment-one-univ -/
theorem momentSum_one_univ (q : Nat) : momentSum q 1 = 2 := by
  simp only [momentSum]
  have hcard : Fintype.card (X 1) = 2 := by rw [X.card_eq_fib]; rfl
  have hsum : ∑ x : X 1, X.fiberMultiplicity x = 2 := by
    rw [X.fiberMultiplicity_sum_eq_pow]; rfl
  have hall : ∀ x : X 1, X.fiberMultiplicity x = 1 := by
    intro x
    have hpos := X.fiberMultiplicity_pos x
    have hle : X.fiberMultiplicity x ≤ 1 := by
      by_contra h; push_neg at h
      have hge2 : X.fiberMultiplicity x ≥ 2 := by omega
      have : ∑ y : X 1, X.fiberMultiplicity y ≥ 3 := by
        calc ∑ y : X 1, X.fiberMultiplicity y
            = X.fiberMultiplicity x + ∑ y ∈ Finset.univ.erase x, X.fiberMultiplicity y := by
              rw [Finset.add_sum_erase _ _ (Finset.mem_univ x)]
          _ ≥ 2 + ∑ y ∈ Finset.univ.erase x, 1 := by
              apply Nat.add_le_add hge2
              apply Finset.sum_le_sum; intro y _; exact X.fiberMultiplicity_pos y
          _ = 2 + (Finset.univ.erase x).card := by simp
          _ = 3 := by
              have := Finset.card_erase_of_mem (Finset.mem_univ x)
              rw [Finset.card_univ, hcard] at this; omega
      omega
    omega
  simp [hall, hcard]

/-- S_q is monotone in q: S_q(m) ≤ S_{q+1}(m) since d(x) ≥ 1.
    pom-moment-mono-q -/
theorem momentSum_mono_q (q m : Nat) (_hq : 1 ≤ q) :
    momentSum q m ≤ momentSum (q + 1) m := by
  simp only [momentSum]
  apply Finset.sum_le_sum; intro x _
  -- d(x)^q ≤ d(x)^(q+1) since d(x) ≥ 1
  calc (X.fiberMultiplicity x) ^ q
      = (X.fiberMultiplicity x) ^ q * 1 := (Nat.mul_one _).symm
    _ ≤ (X.fiberMultiplicity x) ^ q * X.fiberMultiplicity x :=
        Nat.mul_le_mul_left _ (X.fiberMultiplicity_pos x)
    _ = (X.fiberMultiplicity x) ^ (q + 1) := (pow_succ _ _).symm

/-- S_2(m) ≥ 2^m.
    pom-moment-two-ge-pow -/
theorem momentSum_two_ge_pow (m : Nat) : 2 ^ m ≤ momentSum 2 m := by
  rw [← momentSum_one m]; exact momentSum_mono_q 1 m (by omega)

/-- S_q(m) ≥ |X_m| = F(m+1) for all q.
    pom-moment-ge-card -/
theorem momentSum_ge_card (q m : Nat) : Nat.fib (m + 2) ≤ momentSum q m := by
  simp only [momentSum]; rw [← X.card_eq_fib, ← Finset.card_univ]
  rw [Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum; intro x _
  exact Nat.one_le_pow q _ (X.fiberMultiplicity_pos x)

/-- Cauchy-Schwarz for fiber multiplicities: (2^m)² ≤ |X_m| · S_2(m).
    thm:fold-collision-convex-lower-bounds -/
theorem momentSum_cauchy_schwarz (m : Nat) :
    (2 ^ m) ^ 2 ≤ Nat.fib (m + 2) * momentSum 2 m := by
  rw [← momentSum_one, ← momentSum_zero]
  simp only [momentSum, pow_zero, pow_one, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  rw [← Finset.card_univ (α := X m)]
  exact sq_sum_le_card_mul_sum_sq

/-- There exists an element with fiber multiplicity ≥ 2 when m ≥ 2 (pigeonhole: 2^m > F(m+1)). -/
theorem exists_fiber_ge_two (m : Nat) (hm : 2 ≤ m) : ∃ x : X m, 2 ≤ X.fiberMultiplicity x := by
  -- Average fiber multiplicity = 2^m / F(m+1) > 1 for m ≥ 2
  -- So some fiber has multiplicity ≥ 2
  by_contra h
  push_neg at h
  -- All d(x) ≤ 1, so all d(x) = 1 (since d(x) ≥ 1)
  have hall : ∀ x : X m, X.fiberMultiplicity x = 1 := by
    intro x; have := X.fiberMultiplicity_pos x; have := h x; omega
  -- Sum of all d(x) = |X_m| * 1 = F(m+1)
  have hsum : ∑ x : X m, X.fiberMultiplicity x = Nat.fib (m + 2) := by
    simp only [hall, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
      X.card_eq_fib]
  -- But sum = 2^m
  rw [X.fiberMultiplicity_sum_eq_pow] at hsum
  -- 2^m = F(m+1), contradiction for m ≥ 2
  have := fib_le_pow_two m
  -- F(m+1) ≤ 2^m, and if equal then 2^m = F(m+1).
  -- But for m ≥ 2: F(m+1) < 2^m strictly.
  -- F(3) = 3 < 4 = 2^2 for m=2. ✓
  -- Need: strict inequality for m ≥ 2.
  -- For m ≥ 2: F(m+1) < 2^m. Base: F(3)=3 < 4=2^2.
  -- Inductive: F(m+2) = F(m+1)+F(m) < 2^m + 2^(m-1) < 2^(m+1) for m ≥ 2.
  -- Simpler: 2^m ≥ F(m+1) by fib_le_pow_two, and equality would require
  -- all Fibonacci steps to be tight, which fails at m=2.
  -- Use: F 3 = 3 and 2^2 = 4, so strict for m=2.
  -- For m > 2: F(m+1) ≤ F(m) + F(m-1) < 2^(m-1) + 2^(m-2) < 2^m.
  -- Just prove F(m+1) < 2^m for m ≥ 2 by strong induction.
  have hStrict : Nat.fib (m + 2) < 2 ^ m := by
    have key : ∀ n, 2 ≤ n → Nat.fib (n + 2) < 2 ^ n := by
      intro n hn
      induction n with
      | zero => omega
      | succ n ih =>
        cases n with
        | zero => omega
        | succ k =>
          cases k with
          | zero => native_decide
          | succ k =>
            have hR : Nat.fib (k + 5) = Nat.fib (k + 4) + Nat.fib (k + 3) :=
              fib_succ_succ' (k + 3)
            have ihk : Nat.fib (k + 4) < 2 ^ (k + 2) := ih (by omega)
            have ih0 : Nat.fib (k + 3) ≤ 2 ^ (k + 2) := fib_le_pow_two (k + 1)
            calc Nat.fib (k + 2 + 1 + 2) = Nat.fib (k + 4) + Nat.fib (k + 3) := hR
              _ < 2 ^ (k + 2) + 2 ^ (k + 2) := Nat.add_lt_add_of_lt_of_le ihk ih0
              _ = 2 ^ (k + 2 + 1) := by ring
    exact key m hm
  omega

/-- S_q(m) = cMomentSum q m. prop:pom-mixed-collision-kernel-computable. -/
theorem mixed_collision_kernel_computable (q m : Nat) :
    momentSum q m = cMomentSum q m :=
  (cMomentSum_eq q m).symm

/-- The sum of squared fiber multiplicities equals the second moment S_2(m).
    prop:pom-fiberMultiplicity-sum-sq-eq-momentSum-two -/
theorem fiberMultiplicity_sum_sq_eq_momentSum_two (m : Nat) :
    ∑ x : X m, X.fiberMultiplicity x ^ 2 = momentSum 2 m := rfl

end Omega
