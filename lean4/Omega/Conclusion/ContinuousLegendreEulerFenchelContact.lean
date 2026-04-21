import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

namespace Omega.Conclusion

/-- At an interior critical point of `t ↦ (Λ(t) + c) / t`, the quotient-rule derivative vanishes,
forcing the Euler-Fenchel contact identity.
    thm:conclusion-continuous-legendre-euler-fenchel-contact -/
theorem paper_conclusion_continuous_legendre_euler_fenchel_contact
    (Λ Λ' : ℝ → ℝ) (c t : ℝ) (ht : 0 < t) (hΛ : HasDerivAt Λ (Λ' t) t)
    (hcrit : HasDerivAt (fun s => (Λ s + c) / s) 0 t) : t * Λ' t - Λ t = c := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hquot :
      HasDerivAt (fun s => (Λ s + c) / s) (((Λ' t) * t - (Λ t + c)) / t ^ 2) t := by
    simpa [mul_one] using (hΛ.add_const c).div (hasDerivAt_id t) ht0
  have hderiv : (((Λ' t) * t - (Λ t + c)) / t ^ 2) = 0 := HasDerivAt.unique hquot hcrit
  have ht2 : (t ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 ht0
  have hnum : (Λ' t) * t - (Λ t + c) = 0 := by
    rcases (div_eq_zero_iff.mp hderiv) with hnum | hzero
    · exact hnum
    · exact False.elim (ht2 hzero)
  nlinarith

end Omega.Conclusion
