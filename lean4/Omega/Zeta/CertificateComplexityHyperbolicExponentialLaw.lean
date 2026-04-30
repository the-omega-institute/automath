import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Paper label: `cor:xi-certificate-complexity-hyperbolic-exponential-law`. -/
theorem paper_xi_certificate_complexity_hyperbolic_exponential_law
    (r h d N c : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hd : d = Real.log ((1 + r) / (1 - r))) (hh : h = 1 - r)
    (hN : c / h ≤ N) :
    h = 2 / (Real.exp d + 1) ∧ c * (Real.exp d + 1) / 2 ≤ N := by
  have hdenpos : 0 < 1 - r := by linarith
  have hnumpos : 0 < 1 + r := by linarith
  have hratio_pos : 0 < (1 + r) / (1 - r) := div_pos hnumpos hdenpos
  have hexp : Real.exp d = (1 + r) / (1 - r) := by
    rw [hd, Real.exp_log hratio_pos]
  have hheight : h = 2 / (Real.exp d + 1) := by
    rw [hh, hexp]
    field_simp [ne_of_gt hdenpos]
    ring
  refine ⟨hheight, ?_⟩
  have hexp_add_pos : 0 < Real.exp d + 1 := by positivity
  have htwo_div_ne : (2 : ℝ) / (Real.exp d + 1) ≠ 0 := by positivity
  have hN' : c / (2 / (Real.exp d + 1)) ≤ N := by simpa [hheight] using hN
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hN'

end

end Omega.Zeta
