import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.List.GetD
import Omega.POM.FractranPrimeTranslation
import Omega.Zeta.XiCdimLambdaClosedForm

namespace Omega.Zeta

/-- Paper label: `cor:xi-cdim-spectrum-completeness`. Consecutive quotients of the closed-form
residual orders recover the invariant factors one by one, starting from the tail. -/
theorem paper_xi_cdim_spectrum_completeness (factors : List ℕ)
    (hfac : ∀ n ∈ factors, 1 < n) :
    ∀ k : ℕ, k + 1 < factors.length →
      xiCdimLambda factors k / xiCdimLambda factors (k + 1) =
        factors.get! (factors.length - 1 - k) := by
  intro k hk
  let i := factors.length - (k + 1)
  have hi : i < factors.length := by
    dsimp [i]
    omega
  have hi_target : i = factors.length - 1 - k := by
    dsimp [i]
    omega
  have hsub : factors.length - k = i + 1 := by
    dsimp [i]
    omega
  have hstep : xiCdimLambda factors k = factors[i] * xiCdimLambda factors (k + 1) := by
    rw [xiCdimLambda, xiCdimLambda, hsub, List.prod_take_succ, Nat.mul_comm]
  have hden_ne_zero : xiCdimLambda factors (k + 1) ≠ 0 := by
    rw [xiCdimLambda]
    intro hzero
    rw [List.prod_eq_zero_iff] at hzero
    have hz_fac : 0 ∈ factors := (List.take_sublist i factors).subset hzero
    exact Nat.not_lt_zero 1 (hfac 0 hz_fac)
  have hden_pos : 0 < xiCdimLambda factors (k + 1) := Nat.pos_iff_ne_zero.mpr hden_ne_zero
  rw [hstep, Nat.mul_comm, Nat.mul_div_right _ hden_pos]
  have hi' : factors.length - 1 - k < factors.length := by
    omega
  rw [List.get!, List.getD_eq_getElem (l := factors) (d := default) hi']
  simp [hi_target]

end Omega.Zeta
