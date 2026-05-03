import Mathlib.Tactic

namespace Omega.POM

/-- Concrete discriminant-support certificate for the resonance windows `q = 16, 17`. -/
structure pom_resonance_disc_support_q16_q17_data where
  pom_resonance_disc_support_q16_q17_discriminant16 : ℤ
  pom_resonance_disc_support_q16_q17_discriminant17 : ℤ
  pom_resonance_disc_support_q16_q17_delta16 : ℕ
  pom_resonance_disc_support_q16_q17_delta17 : ℕ
  pom_resonance_disc_support_q16_q17_delta16_pos :
    0 < pom_resonance_disc_support_q16_q17_delta16
  pom_resonance_disc_support_q16_q17_delta17_pos :
    0 < pom_resonance_disc_support_q16_q17_delta17
  pom_resonance_disc_support_q16_q17_disc16_factorization :
    pom_resonance_disc_support_q16_q17_discriminant16 =
      -((2 ^ 58 * 3 ^ 4 * 7 ^ 2 * 59 *
        pom_resonance_disc_support_q16_q17_delta16 : ℕ) : ℤ)
  pom_resonance_disc_support_q16_q17_disc17_factorization :
    pom_resonance_disc_support_q16_q17_discriminant17 =
      -((2 ^ 100 * 3 ^ 28 * 5 ^ 9 * 7 ^ 3 * 11 ^ 2 * 13 ^ 3 * 17 ^ 2 *
        pom_resonance_disc_support_q16_q17_delta17 : ℕ) : ℤ)
  pom_resonance_disc_support_q16_q17_v2_disc16 :
    2 ^ 58 ∣ pom_resonance_disc_support_q16_q17_discriminant16.natAbs ∧
      ¬ 2 ^ 59 ∣ pom_resonance_disc_support_q16_q17_discriminant16.natAbs
  pom_resonance_disc_support_q16_q17_v2_disc17 :
    2 ^ 100 ∣ pom_resonance_disc_support_q16_q17_discriminant17.natAbs ∧
      ¬ 2 ^ 101 ∣ pom_resonance_disc_support_q16_q17_discriminant17.natAbs
  pom_resonance_disc_support_q16_q17_delta16_coprime_audit :
    ∀ p : ℕ, p.Prime → p ≤ 20000 →
      p ∣ pom_resonance_disc_support_q16_q17_delta16 → False
  pom_resonance_disc_support_q16_q17_delta17_coprime_audit :
    ∀ p : ℕ, p.Prime → p ≤ 20000 →
      p ∣ pom_resonance_disc_support_q16_q17_delta17 → False

namespace pom_resonance_disc_support_q16_q17_data

/-- The claimed ramified-prime support, signs, and audited residual coprimality. -/
def statement (D : pom_resonance_disc_support_q16_q17_data) : Prop :=
  D.pom_resonance_disc_support_q16_q17_discriminant16 < 0 ∧
    D.pom_resonance_disc_support_q16_q17_discriminant17 < 0 ∧
    2 ^ 58 ∣ D.pom_resonance_disc_support_q16_q17_discriminant16.natAbs ∧
    ¬ 2 ^ 59 ∣ D.pom_resonance_disc_support_q16_q17_discriminant16.natAbs ∧
    2 ^ 100 ∣ D.pom_resonance_disc_support_q16_q17_discriminant17.natAbs ∧
    ¬ 2 ^ 101 ∣ D.pom_resonance_disc_support_q16_q17_discriminant17.natAbs ∧
    3 ∣ D.pom_resonance_disc_support_q16_q17_discriminant16.natAbs ∧
    7 ∣ D.pom_resonance_disc_support_q16_q17_discriminant16.natAbs ∧
    59 ∣ D.pom_resonance_disc_support_q16_q17_discriminant16.natAbs ∧
    3 ∣ D.pom_resonance_disc_support_q16_q17_discriminant17.natAbs ∧
    5 ∣ D.pom_resonance_disc_support_q16_q17_discriminant17.natAbs ∧
    7 ∣ D.pom_resonance_disc_support_q16_q17_discriminant17.natAbs ∧
    11 ∣ D.pom_resonance_disc_support_q16_q17_discriminant17.natAbs ∧
    13 ∣ D.pom_resonance_disc_support_q16_q17_discriminant17.natAbs ∧
    17 ∣ D.pom_resonance_disc_support_q16_q17_discriminant17.natAbs ∧
    (∀ p : ℕ, p.Prime → p ≤ 20000 →
      p ∣ D.pom_resonance_disc_support_q16_q17_delta16 → False) ∧
    (∀ p : ℕ, p.Prime → p ≤ 20000 →
      p ∣ D.pom_resonance_disc_support_q16_q17_delta17 → False)

end pom_resonance_disc_support_q16_q17_data

/-- Data-parametrized certificate retained from the upstream module. -/
theorem pom_resonance_disc_support_q16_q17_data_statement_of_certificate
    (D : pom_resonance_disc_support_q16_q17_data) : D.statement := by
  rw [pom_resonance_disc_support_q16_q17_data.statement]
  have hdisc16_abs :
      D.pom_resonance_disc_support_q16_q17_discriminant16.natAbs =
        2 ^ 58 * 3 ^ 4 * 7 ^ 2 * 59 *
          D.pom_resonance_disc_support_q16_q17_delta16 := by
    rw [D.pom_resonance_disc_support_q16_q17_disc16_factorization]
    rw [Int.natAbs_neg, Int.natAbs_natCast]
  have hdisc17_abs :
      D.pom_resonance_disc_support_q16_q17_discriminant17.natAbs =
        2 ^ 100 * 3 ^ 28 * 5 ^ 9 * 7 ^ 3 * 11 ^ 2 * 13 ^ 3 * 17 ^ 2 *
          D.pom_resonance_disc_support_q16_q17_delta17 := by
    rw [D.pom_resonance_disc_support_q16_q17_disc17_factorization]
    rw [Int.natAbs_neg, Int.natAbs_natCast]
  have hdisc16_neg : D.pom_resonance_disc_support_q16_q17_discriminant16 < 0 := by
    rw [D.pom_resonance_disc_support_q16_q17_disc16_factorization]
    apply neg_neg_of_pos
    exact_mod_cast Nat.mul_pos (by norm_num) D.pom_resonance_disc_support_q16_q17_delta16_pos
  have hdisc17_neg : D.pom_resonance_disc_support_q16_q17_discriminant17 < 0 := by
    rw [D.pom_resonance_disc_support_q16_q17_disc17_factorization]
    apply neg_neg_of_pos
    exact_mod_cast Nat.mul_pos (by norm_num) D.pom_resonance_disc_support_q16_q17_delta17_pos
  refine ⟨hdisc16_neg, hdisc17_neg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    D.pom_resonance_disc_support_q16_q17_delta16_coprime_audit,
    D.pom_resonance_disc_support_q16_q17_delta17_coprime_audit⟩
  · exact D.pom_resonance_disc_support_q16_q17_v2_disc16.1
  · exact D.pom_resonance_disc_support_q16_q17_v2_disc16.2
  · exact D.pom_resonance_disc_support_q16_q17_v2_disc17.1
  · exact D.pom_resonance_disc_support_q16_q17_v2_disc17.2
  · rw [hdisc16_abs]
    exact dvd_mul_of_dvd_left (by norm_num : 3 ∣ 2 ^ 58 * 3 ^ 4 * 7 ^ 2 * 59) _
  · rw [hdisc16_abs]
    exact dvd_mul_of_dvd_left (by norm_num : 7 ∣ 2 ^ 58 * 3 ^ 4 * 7 ^ 2 * 59) _
  · rw [hdisc16_abs]
    exact dvd_mul_of_dvd_left (by norm_num : 59 ∣ 2 ^ 58 * 3 ^ 4 * 7 ^ 2 * 59) _
  · rw [hdisc17_abs]
    exact dvd_mul_of_dvd_left
      (by norm_num : 3 ∣ 2 ^ 100 * 3 ^ 28 * 5 ^ 9 * 7 ^ 3 * 11 ^ 2 * 13 ^ 3 *
        17 ^ 2) _
  · rw [hdisc17_abs]
    exact dvd_mul_of_dvd_left
      (by norm_num : 5 ∣ 2 ^ 100 * 3 ^ 28 * 5 ^ 9 * 7 ^ 3 * 11 ^ 2 * 13 ^ 3 *
        17 ^ 2) _
  · rw [hdisc17_abs]
    exact dvd_mul_of_dvd_left
      (by norm_num : 7 ∣ 2 ^ 100 * 3 ^ 28 * 5 ^ 9 * 7 ^ 3 * 11 ^ 2 * 13 ^ 3 *
        17 ^ 2) _
  · rw [hdisc17_abs]
    exact dvd_mul_of_dvd_left
      (by norm_num : 11 ∣ 2 ^ 100 * 3 ^ 28 * 5 ^ 9 * 7 ^ 3 * 11 ^ 2 * 13 ^ 3 *
        17 ^ 2) _
  · rw [hdisc17_abs]
    exact dvd_mul_of_dvd_left
      (by norm_num : 13 ∣ 2 ^ 100 * 3 ^ 28 * 5 ^ 9 * 7 ^ 3 * 11 ^ 2 * 13 ^ 3 *
        17 ^ 2) _
  · rw [hdisc17_abs]
    exact dvd_mul_of_dvd_left
      (by norm_num : 17 ∣ 2 ^ 100 * 3 ^ 28 * 5 ^ 9 * 7 ^ 3 * 11 ^ 2 * 13 ^ 3 *
        17 ^ 2) _

/-- The audited discriminant of the `q = 16` resonance polynomial. -/
def pom_resonance_disc_support_q16_q17_disc16 : ℤ :=
  -743612256394218108622650819414988157289154213196172880088436924201072900799330663280133426916773049149057494501115766645923115714058132393595764736

/-- The audited discriminant of the `q = 17` resonance polynomial. -/
def pom_resonance_disc_support_q16_q17_disc17 : ℤ :=
  -1488269947647776824900783219332903680175872394391398716989435899454757080223990438237756608794756586111676213680689724744720518011178698463848910934519216254634229139947203924535361404928000000000

/-- The `q = 16` leftover factor after the displayed ramified prime powers. -/
def pom_resonance_disc_support_q16_q17_delta16 : ℕ :=
  11017262070804110968782159151431112243023834806581855472029743457398900381866596306758939428543074167920904104311185818881289

/-- The `q = 17` leftover factor after the displayed ramified prime powers. -/
def pom_resonance_disc_support_q16_q17_delta17 : ℕ :=
  997124953047621001864713678014001900392334747274878665091140732114251157239680027533983511369879821244920916271306620897366254950750899

/-- Prime support listed for the `q = 16` discriminant below the audit bound. -/
def pom_resonance_disc_support_q16_q17_support16 : List ℕ :=
  [2, 3, 7, 59]

/-- Prime support listed for the `q = 17` discriminant below the audit bound. -/
def pom_resonance_disc_support_q16_q17_support17 : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17]

/-- Boolean audit that the `q = 16` leftover has no prime factor at most `20000`. -/
def pom_resonance_disc_support_q16_q17_delta16_no_small_prime_factor : Bool :=
  (List.range 20001).all fun p =>
    decide (Nat.Prime p → ¬ p ∣ pom_resonance_disc_support_q16_q17_delta16)

/-- Boolean audit that the `q = 17` leftover has no prime factor at most `20000`. -/
def pom_resonance_disc_support_q16_q17_delta17_no_small_prime_factor : Bool :=
  (List.range 20001).all fun p =>
    decide (Nat.Prime p → ¬ p ∣ pom_resonance_disc_support_q16_q17_delta17)

/-- Boolean audit that every listed `q = 16` prime divides the discriminant. -/
def pom_resonance_disc_support_q16_q17_listed_divisibility16 : Bool :=
  pom_resonance_disc_support_q16_q17_support16.all fun p =>
    decide (p ∣ Int.natAbs pom_resonance_disc_support_q16_q17_disc16)

/-- Boolean audit that every listed `q = 17` prime divides the discriminant. -/
def pom_resonance_disc_support_q16_q17_listed_divisibility17 : Bool :=
  pom_resonance_disc_support_q16_q17_support17.all fun p =>
    decide (p ∣ Int.natAbs pom_resonance_disc_support_q16_q17_disc17)

/-- Concrete certificate for the two generated discriminant factorizations and their audited
small-prime ramification support. -/
def pom_resonance_disc_support_q16_q17_statement : Prop :=
  pom_resonance_disc_support_q16_q17_disc16 =
      -((2 : ℤ) ^ 58 * 3 ^ 4 * 7 ^ 2 * 59 *
        pom_resonance_disc_support_q16_q17_delta16) ∧
    pom_resonance_disc_support_q16_q17_disc17 =
      -((2 : ℤ) ^ 100 * 3 ^ 28 * 5 ^ 9 * 7 ^ 3 * 11 ^ 2 * 13 ^ 3 * 17 ^ 2 *
        pom_resonance_disc_support_q16_q17_delta17) ∧
    pom_resonance_disc_support_q16_q17_disc16 < 0 ∧
    pom_resonance_disc_support_q16_q17_disc17 < 0 ∧
    pom_resonance_disc_support_q16_q17_delta16_no_small_prime_factor = true ∧
    pom_resonance_disc_support_q16_q17_delta17_no_small_prime_factor = true ∧
    pom_resonance_disc_support_q16_q17_listed_divisibility16 = true ∧
    pom_resonance_disc_support_q16_q17_listed_divisibility17 = true ∧
    ((2 : ℕ) ^ 58 ∣ Int.natAbs pom_resonance_disc_support_q16_q17_disc16 ∧
      ¬ (2 : ℕ) ^ 59 ∣ Int.natAbs pom_resonance_disc_support_q16_q17_disc16) ∧
    ((2 : ℕ) ^ 100 ∣ Int.natAbs pom_resonance_disc_support_q16_q17_disc17 ∧
      ¬ (2 : ℕ) ^ 101 ∣ Int.natAbs pom_resonance_disc_support_q16_q17_disc17)

/-- Paper label: `prop:pom-resonance-disc-support-q16-q17`. -/
theorem paper_pom_resonance_disc_support_q16_q17 :
    pom_resonance_disc_support_q16_q17_statement := by
  unfold pom_resonance_disc_support_q16_q17_statement
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

end Omega.POM
