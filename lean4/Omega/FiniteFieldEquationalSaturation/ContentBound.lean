import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.FiniteFieldEquationalSaturation

/-- A finite two-variable integral coefficient certificate for the content bound. -/
structure finite_field_content_bound_data where
  p : ℕ
  coeff : (Fin 2 →₀ ℕ) → ℤ
  support : Finset (Fin 2 →₀ ℕ)
  coeff_eq_zero_of_not_mem_support : ∀ m, m ∉ support → coeff m = 0
  support_nonempty : support.Nonempty
  content : ℤ
  content_dvd_iff_coeff_dvd : ∀ q : ℤ, q ∣ content ↔ ∀ m, q ∣ coeff m

namespace finite_field_content_bound_data

/-- Reduction of the certified integral polynomial to all coefficients modulo `p`. -/
def finite_field_content_bound_reduction_zero (D : finite_field_content_bound_data) : Prop :=
  ∀ m : Fin 2 →₀ ℕ, (D.coeff m : ZMod D.p) = 0

/-- The content certificate predicts exactly when reduction modulo `p` vanishes. -/
def finite_field_content_bound_statement (D : finite_field_content_bound_data) : Prop :=
  D.finite_field_content_bound_reduction_zero ↔ (D.p : ℤ) ∣ D.content

end finite_field_content_bound_data

open finite_field_content_bound_data

/-- thm:finite-field-content-bound -/
theorem paper_finite_field_content_bound (D : finite_field_content_bound_data) :
    finite_field_content_bound_statement D := by
  constructor
  · intro hzero
    rw [D.content_dvd_iff_coeff_dvd]
    intro m
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (D.coeff m) D.p).mp (hzero m)
  · intro hcontent m
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact (D.content_dvd_iff_coeff_dvd (D.p : ℤ)).mp hcontent m

end Omega.FiniteFieldEquationalSaturation
