import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

universe u

namespace Omega.Folding

/-- Positive part of a real number. -/
def truncPositive (x : ℝ) : ℝ :=
  max x 0

/-- Truncated oracle success written on a finite probability vector. -/
def oracleSuccess {α : Type u} [Fintype α] (π : α → ℝ) (t : ℝ) : ℝ :=
  ∑ x, min (π x) t

/-- The complementary positive-part error term. -/
def oracleFailure {α : Type u} [Fintype α] (π : α → ℝ) (t : ℝ) : ℝ :=
  ∑ x, truncPositive (π x - t)

/-- The finite Rényi mass of order `q`. -/
def renyiMass {α : Type u} [Fintype α] (q : ℕ) (π : α → ℝ) : ℝ :=
  ∑ x, π x ^ q

lemma min_add_truncPositive (a t : ℝ) :
    min a t + truncPositive (a - t) = a := by
  by_cases h : a ≤ t
  · simp [truncPositive, h, sub_nonpos.mpr h]
  · have ht : t ≤ a := le_of_not_ge h
    simp [truncPositive, min_eq_right ht, sub_nonneg.mpr ht]

lemma oracle_success_add_failure {α : Type u} [Fintype α] (π : α → ℝ) (t : ℝ)
    (hπsum : ∑ x, π x = 1) :
    oracleSuccess π t + oracleFailure π t = 1 := by
  calc
    oracleSuccess π t + oracleFailure π t
        = ∑ x, (min (π x) t + truncPositive (π x - t)) := by
            simp [oracleSuccess, oracleFailure, Finset.sum_add_distrib]
    _ = ∑ x, π x := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          exact min_add_truncPositive (π x) t
    _ = 1 := hπsum

lemma oracle_failure_eq_one_sub_success {α : Type u} [Fintype α] (π : α → ℝ) (t : ℝ)
    (hπsum : ∑ x, π x = 1) :
    1 - oracleSuccess π t = oracleFailure π t := by
  have hsum := oracle_success_add_failure π t hπsum
  linarith

lemma truncPositive_le_renyi_pointwise (a t : ℝ) {q : ℕ}
    (ha : 0 ≤ a) (ht : 0 < t) (hq : 1 < q) :
    truncPositive (a - t) ≤ a ^ q / t ^ (q - 1) := by
  by_cases hat : a ≤ t
  · have hright : 0 ≤ a ^ q / t ^ (q - 1) := by positivity
    simp [truncPositive, sub_nonpos.mpr hat, hright]
  · have hta : t ≤ a := le_of_not_ge hat
    have htrunc : truncPositive (a - t) = a - t := by
      simp [truncPositive, sub_nonneg.mpr hta]
    have hpow : t ^ (q - 1) ≤ a ^ (q - 1) := by
      exact pow_le_pow_left₀ (le_of_lt ht) hta (q - 1)
    have hmul : a * t ^ (q - 1) ≤ a * a ^ (q - 1) := by
      gcongr
    have hqeq : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.one_le_of_lt hq)
    have ha_le : a ≤ a ^ q / t ^ (q - 1) := by
      have htpow : 0 < t ^ (q - 1) := pow_pos ht _
      exact (le_div_iff₀ htpow).2 <| by
        calc
          a * t ^ (q - 1) ≤ a * a ^ (q - 1) := hmul
          _ = a ^ (q - 1 + 1) := by rw [pow_succ']
          _ = a ^ q := by rw [hqeq]
    calc
      truncPositive (a - t) = a - t := htrunc
      _ ≤ a := by linarith
      _ ≤ a ^ q / t ^ (q - 1) := ha_le

lemma oracle_failure_le_renyi_mass {α : Type*} [Fintype α] (π : α → ℝ) (t : ℝ) {q : ℕ}
    (hπ : ∀ x, 0 ≤ π x) (ht : 0 < t) (hq : 1 < q) :
    oracleFailure π t ≤ renyiMass q π / t ^ (q - 1) := by
  calc
    oracleFailure π t = ∑ x, truncPositive (π x - t) := rfl
    _ ≤ ∑ x, π x ^ q / t ^ (q - 1) := by
          refine Finset.sum_le_sum ?_
          intro x hx
          exact truncPositive_le_renyi_pointwise (π x) t (hπ x) ht hq
    _ = renyiMass q π / t ^ (q - 1) := by
          simp [renyiMass, Finset.sum_div]

/-- Concrete nonasymptotic oracle error package: the truncation identity
`1 - Succ = Σ (π - t)₊` and the Rényi bound obtained by summing the pointwise estimate
`(a - t)₊ ≤ a^q / t^(q - 1)`. -/
def oracleRenyiNonasymptoticErrorBoundStatement : Prop :=
  ∀ {α : Type u} [Fintype α] (π : α → ℝ) (t : ℝ) (q : ℕ),
    (∀ x, 0 ≤ π x) →
      (∑ x, π x = 1) →
      0 < t →
      1 < q →
      1 - oracleSuccess π t = oracleFailure π t ∧
        oracleFailure π t ≤ renyiMass q π / t ^ (q - 1) ∧
        1 - oracleSuccess π t ≤ renyiMass q π / t ^ (q - 1)

/-- Paper-facing wrapper for the oracle Rényi nonasymptotic error estimate.
    thm:oracle-renyi-nonasymptotic-error-bound -/
def paper_oracle_renyi_nonasymptotic_error_bound : Prop :=
  ∀ {α : Type u} [Fintype α] (π : α → ℝ) (t : ℝ) (q : ℕ),
    (∀ x, 0 ≤ π x) →
      (∑ x, π x = 1) →
      0 < t →
      1 < q →
      1 - oracleSuccess π t = oracleFailure π t ∧
        oracleFailure π t ≤ renyiMass q π / t ^ (q - 1) ∧
        1 - oracleSuccess π t ≤ renyiMass q π / t ^ (q - 1)

theorem paper_oracle_renyi_nonasymptotic_error_bound_proof :
    paper_oracle_renyi_nonasymptotic_error_bound := by
  intro α _ π t q hπ hπsum ht hq
  have hid : 1 - oracleSuccess π t = oracleFailure π t :=
    oracle_failure_eq_one_sub_success π t hπsum
  have hbound : oracleFailure π t ≤ renyiMass q π / t ^ (q - 1) :=
    oracle_failure_le_renyi_mass π t hπ ht hq
  refine ⟨hid, hbound, ?_⟩
  simpa [hid] using hbound

end Omega.Folding
