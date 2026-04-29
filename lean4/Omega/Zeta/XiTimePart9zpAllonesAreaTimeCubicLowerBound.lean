import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete counting/coding package for reversible all-ones lifts.  The side-information and
quadratic stopping-time lower bounds are recorded with rational rates so their product gives the
area-time cubic lower bound by ordered-ring arithmetic. -/
structure xi_time_part9zp_allones_area_time_cubic_lower_bound_data where
  alphabetSize : ℕ
  alphabetSize_ge_two : 2 ≤ alphabetSize
  sideLength : ℕ → ℕ
  stoppingTime : ℕ → ℕ
  codingRate : ℚ
  timeRate : ℚ
  areaTimeRate : ℚ
  threshold : ℕ
  codingRate_nonneg : 0 ≤ codingRate
  timeRate_nonneg : 0 ≤ timeRate
  areaTimeRate_eq : areaTimeRate = codingRate * timeRate
  allones_reduction_length : ∀ m : ℕ, stoppingTime m = m ^ 2 / 4
  side_information_lower :
    ∀ m : ℕ, threshold ≤ m → codingRate * (m : ℚ) ≤ sideLength m
  quadratic_stopping_lower :
    ∀ m : ℕ, threshold ≤ m → timeRate * (m : ℚ) ^ 2 ≤ stoppingTime m

/-- Paper-facing all-ones area-time lower-bound statement. -/
def xi_time_part9zp_allones_area_time_cubic_lower_bound_statement
    (D : xi_time_part9zp_allones_area_time_cubic_lower_bound_data) : Prop :=
  (∀ m : ℕ, D.stoppingTime m = m ^ 2 / 4) ∧
    ∀ m : ℕ, D.threshold ≤ m →
      D.areaTimeRate * (m : ℚ) ^ 3 ≤ (D.sideLength m : ℚ) * (D.stoppingTime m : ℚ)

/-- Paper label: `thm:xi-time-part9zp-allones-area-time-cubic-lower-bound`. -/
theorem paper_xi_time_part9zp_allones_area_time_cubic_lower_bound
    (D : xi_time_part9zp_allones_area_time_cubic_lower_bound_data) :
    xi_time_part9zp_allones_area_time_cubic_lower_bound_statement D := by
  constructor
  · exact D.allones_reduction_length
  · intro m hm
    have hside : D.codingRate * (m : ℚ) ≤ D.sideLength m :=
      D.side_information_lower m hm
    have htime : D.timeRate * (m : ℚ) ^ 2 ≤ D.stoppingTime m :=
      D.quadratic_stopping_lower m hm
    have htime_nonneg : 0 ≤ D.timeRate * (m : ℚ) ^ 2 :=
      mul_nonneg D.timeRate_nonneg (sq_nonneg _)
    have hside_nonneg : 0 ≤ (D.sideLength m : ℚ) := by exact_mod_cast Nat.zero_le _
    calc
      D.areaTimeRate * (m : ℚ) ^ 3 =
          (D.codingRate * (m : ℚ)) * (D.timeRate * (m : ℚ) ^ 2) := by
            rw [D.areaTimeRate_eq]
            ring_nf
      _ ≤ (D.sideLength m : ℚ) * (D.stoppingTime m : ℚ) :=
          mul_le_mul hside htime htime_nonneg hside_nonneg

end Omega.Zeta
