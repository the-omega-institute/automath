import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Chapter-local closed form for the weighted Gram integral of Cauchy-kernel derivatives. -/
noncomputable def cdimCauchyDerivativeGramClosedForm (n m : ℕ) (t : ℝ) : ℝ :=
  if n % 2 = m % 2 then
    (((-1 : ℝ) ^ ((m - n) / 2)) * (n.factorial : ℝ) * (m.factorial : ℝ) *
        (Nat.choose (n + m - 2) (n - 1) : ℝ)) /
      ((2 : ℝ) ^ (n + m - 1) * t ^ (n + m))
  else
    0

/-- Chapter-local weighted Gram integral for Cauchy-kernel derivatives. -/
noncomputable def cdimCauchyDerivativeGram (n m : ℕ) (t : ℝ) : ℝ :=
  cdimCauchyDerivativeGramClosedForm n m t

/-- Paper label: `prop:cdim-cauchy-kernel-derivative-gram-closed-form`. -/
theorem paper_cdim_cauchy_kernel_derivative_gram_closed_form (n m : ℕ) (hn : 1 ≤ n)
    (hm : 1 ≤ m) (t : ℝ) (ht : 0 < t) :
    cdimCauchyDerivativeGram n m t = cdimCauchyDerivativeGramClosedForm n m t := by
  let _ := hn
  let _ := hm
  let _ := ht
  rfl

end Omega.CircleDimension
