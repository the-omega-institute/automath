import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Nat.Prime.Basic
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

/-- Paper label: `prop:pom-resonance-disc-support-q16-q17`. -/
theorem paper_pom_resonance_disc_support_q16_q17
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

end Omega.POM
