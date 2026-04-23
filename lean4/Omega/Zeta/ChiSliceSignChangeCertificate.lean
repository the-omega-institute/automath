import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:chi-slice-sign-change-certificate`. -/
theorem paper_chi_slice_sign_change_certificate (f : Real -> Real) (a b : Real)
    (hcont : Continuous f) (hab : a <= b) (hsign : f a * f b <= 0) :
    ∃ t ∈ Set.Icc a b, f t = 0 := by
  by_cases hfa : f a = 0
  · exact ⟨a, ⟨le_rfl, hab⟩, hfa⟩
  by_cases hfb : f b = 0
  · exact ⟨b, ⟨hab, le_rfl⟩, hfb⟩
  by_cases hfa_nonneg : 0 ≤ f a
  · have hfa_pos : 0 < f a := by
      apply lt_of_le_of_ne hfa_nonneg
      simpa [eq_comm] using hfa
    have hfb_nonpos : f b ≤ 0 := by
      nlinarith
    have hfb_neg : f b < 0 := lt_of_le_of_ne hfb_nonpos hfb
    have hzero_mem : (0 : Real) ∈ Set.Icc (f b) (f a) := ⟨le_of_lt hfb_neg, le_of_lt hfa_pos⟩
    rcases intermediate_value_Icc' hab hcont.continuousOn hzero_mem with ⟨t, ht, hft⟩
    exact ⟨t, ht, hft⟩
  · have hfa_neg : f a < 0 := lt_of_not_ge hfa_nonneg
    have hfb_nonneg : 0 ≤ f b := by
      nlinarith
    have hfb_pos : 0 < f b := by
      apply lt_of_le_of_ne hfb_nonneg
      simpa [eq_comm] using hfb
    have hzero_mem : (0 : Real) ∈ Set.Icc (f a) (f b) := ⟨le_of_lt hfa_neg, le_of_lt hfb_pos⟩
    rcases intermediate_value_Icc hab hcont.continuousOn hzero_mem with ⟨t, ht, hft⟩
    exact ⟨t, ht, hft⟩

end Omega.Zeta
