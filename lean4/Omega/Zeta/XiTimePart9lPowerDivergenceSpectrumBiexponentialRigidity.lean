import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9l-power-divergence-spectrum-biexponential-rigidity`. -/
theorem paper_xi_time_part9l_power_divergence_spectrum_biexponential_rigidity
    (L α : ℝ) (hL : 0 < L) (hα : 1 < α) :
    let E : ℝ → ℝ := fun a => Real.exp ((2 * a - 1) * L) + Real.exp ((a - 2) * L)
    deriv (deriv E) α - 3 * L * deriv E α + 2 * L ^ 2 * E α = 0 ∧
      0 < L ^ 2 * Real.exp ((α + 1) * L) / (1 + Real.exp ((α + 1) * L)) ^ 2 := by
  have _ := hα
  let E : ℝ → ℝ := fun a => Real.exp ((2 * a - 1) * L) + Real.exp ((a - 2) * L)
  have hleft_exp (a : ℝ) :
      HasDerivAt (fun a : ℝ => Real.exp ((2 * a - 1) * L))
        ((2 * L) * Real.exp ((2 * a - 1) * L)) a := by
    have htwo : HasDerivAt (fun a : ℝ => (2 : ℝ) * a) 2 a := by
      simpa using (hasDerivAt_const (x := a) (c := (2 : ℝ))).mul (hasDerivAt_id a)
    have hsub : HasDerivAt (fun a : ℝ => (2 : ℝ) * a - 1) 2 a := by
      convert htwo.sub (hasDerivAt_const (x := a) (c := (1 : ℝ))) using 1
      · norm_num
    have hlin : HasDerivAt (fun a : ℝ => ((2 : ℝ) * a - 1) * L) (2 * L) a := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hsub.mul_const L
    simpa [mul_comm, mul_left_comm, mul_assoc] using hlin.exp
  have hright_exp (a : ℝ) :
      HasDerivAt (fun a : ℝ => Real.exp ((a - 2) * L))
        (L * Real.exp ((a - 2) * L)) a := by
    have hsub : HasDerivAt (fun a : ℝ => a - 2) 1 a := by
      convert (hasDerivAt_id a).sub (hasDerivAt_const (x := a) (c := (2 : ℝ))) using 1
      · norm_num
    have hlin : HasDerivAt (fun a : ℝ => (a - 2) * L) L a := by
      simpa using hsub.mul_const L
    simpa [mul_comm, mul_left_comm, mul_assoc] using hlin.exp
  have hderiv (a : ℝ) :
      deriv E a =
        2 * L * Real.exp ((2 * a - 1) * L) + L * Real.exp ((a - 2) * L) := by
    unfold E
    exact ((hleft_exp a).add (hright_exp a)).deriv
  have hderiv2 (a : ℝ) :
      deriv (deriv E) a =
        (2 * L) ^ 2 * Real.exp ((2 * a - 1) * L) +
          L ^ 2 * Real.exp ((a - 2) * L) := by
    have hfun :
        deriv E =
          fun a : ℝ =>
            2 * L * Real.exp ((2 * a - 1) * L) + L * Real.exp ((a - 2) * L) := by
      funext a
      exact hderiv a
    rw [hfun]
    have hleft :
        HasDerivAt
          (fun a : ℝ => 2 * L * Real.exp ((2 * a - 1) * L))
          ((2 * L) ^ 2 * Real.exp ((2 * a - 1) * L)) a := by
      convert (hleft_exp a).const_mul (2 * L) using 1
      ring
    have hright :
        HasDerivAt
          (fun a : ℝ => L * Real.exp ((a - 2) * L))
          (L ^ 2 * Real.exp ((a - 2) * L)) a := by
      convert (hright_exp a).const_mul L using 1
      ring
    exact (hleft.add hright).deriv
  refine ⟨?_, ?_⟩
  · rw [hderiv2, hderiv]
    change
      (2 * L) ^ 2 * Real.exp ((2 * α - 1) * L) +
            L ^ 2 * Real.exp ((α - 2) * L) -
          3 * L *
            (2 * L * Real.exp ((2 * α - 1) * L) +
              L * Real.exp ((α - 2) * L)) +
        2 * L ^ 2 *
          (Real.exp ((2 * α - 1) * L) + Real.exp ((α - 2) * L)) =
        0
    ring
  · positivity

end Omega.Zeta
