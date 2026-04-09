import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- `5 ∤ 1!`.
    prop:pom-first-joint-nonsemisimple-threshold -/
theorem five_not_dvd_fact_one : ¬ (5 : ℕ) ∣ Nat.factorial 1 := by decide

/-- `5 ∤ 2!`.
    prop:pom-first-joint-nonsemisimple-threshold -/
theorem five_not_dvd_fact_two : ¬ (5 : ℕ) ∣ Nat.factorial 2 := by decide

/-- `5 ∤ 3!`.
    prop:pom-first-joint-nonsemisimple-threshold -/
theorem five_not_dvd_fact_three : ¬ (5 : ℕ) ∣ Nat.factorial 3 := by decide

/-- `5 ∤ 4!`.
    prop:pom-first-joint-nonsemisimple-threshold -/
theorem five_not_dvd_fact_four : ¬ (5 : ℕ) ∣ Nat.factorial 4 := by decide

/-- `5 ∣ 5!`.
    prop:pom-first-joint-nonsemisimple-threshold -/
theorem five_dvd_fact_five : (5 : ℕ) ∣ Nat.factorial 5 := by decide

/-- For `q ≥ 5`, `5 ∣ q!`.
    prop:pom-first-joint-nonsemisimple-threshold -/
theorem five_dvd_fact_of_ge_five (q : ℕ) (hq : 5 ≤ q) :
    (5 : ℕ) ∣ Nat.factorial q :=
  dvd_trans five_dvd_fact_five (Nat.factorial_dvd_factorial hq)

/-- For `q < 5`, `5 ∤ q!`.
    prop:pom-first-joint-nonsemisimple-threshold -/
theorem five_not_dvd_fact_of_lt_five (q : ℕ) (hq : q < 5) :
    ¬ (5 : ℕ) ∣ Nat.factorial q := by
  interval_cases q
  · decide
  · exact five_not_dvd_fact_one
  · exact five_not_dvd_fact_two
  · exact five_not_dvd_fact_three
  · exact five_not_dvd_fact_four

/-- Threshold iff: `5 ∣ q! ↔ 5 ≤ q`.
    prop:pom-first-joint-nonsemisimple-threshold -/
theorem five_dvd_fact_iff (q : ℕ) : (5 : ℕ) ∣ Nat.factorial q ↔ 5 ≤ q := by
  refine ⟨fun h => ?_, five_dvd_fact_of_ge_five q⟩
  by_contra hlt
  push_neg at hlt
  exact five_not_dvd_fact_of_lt_five q hlt h

/-- Paper package: POM first joint (p, q) = (5, 5) non-semisimple threshold.
    prop:pom-first-joint-nonsemisimple-threshold -/
theorem paper_pom_first_joint_nonsemisimple_threshold :
    (¬ (5 : ℕ) ∣ Nat.factorial 4) ∧
    ((5 : ℕ) ∣ Nat.factorial 5) ∧
    (∀ q : ℕ, (5 : ℕ) ∣ Nat.factorial q ↔ 5 ≤ q) ∧
    (∀ q : ℕ, 5 ≤ q → (5 : ℕ) ∣ Nat.factorial q) ∧
    (∀ q : ℕ, q < 5 → ¬ (5 : ℕ) ∣ Nat.factorial q) ∧
    ((5 : ℕ) ∣ Nat.factorial 5 ∧ ∀ q : ℕ, q < 5 → ¬ (5 : ℕ) ∣ Nat.factorial q) :=
  ⟨five_not_dvd_fact_four,
   five_dvd_fact_five,
   five_dvd_fact_iff,
   five_dvd_fact_of_ge_five,
   five_not_dvd_fact_of_lt_five,
   ⟨five_dvd_fact_five, five_not_dvd_fact_of_lt_five⟩⟩

end Omega.POM
