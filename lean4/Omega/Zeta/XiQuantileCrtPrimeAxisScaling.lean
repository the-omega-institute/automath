import Mathlib.Tactic

namespace Omega.Zeta

/-- Product over the selected CRT axes. -/
def xi_quantile_crt_prime_axis_scaling_axis_product {K : ℕ} (axis : Fin K → ℕ) : ℕ :=
  ∏ i, axis i

/-- Concrete finite package for monotonic replacement of prime-axis choices. -/
structure xi_quantile_crt_prime_axis_scaling_data where
  K : ℕ
  threshold : ℕ
  minimalAxis : Fin K → ℕ
  replacementAxis : Fin K → ℕ
  axis_le_replacement : ∀ i, minimalAxis i ≤ replacementAxis i
  minimalAxis_reaches_threshold :
    threshold ≤ xi_quantile_crt_prime_axis_scaling_axis_product minimalAxis

/-- The threshold still holds after replacing axes by larger ones. -/
def xi_quantile_crt_prime_axis_scaling_data.claim
    (D : xi_quantile_crt_prime_axis_scaling_data) : Prop :=
  D.threshold ≤ xi_quantile_crt_prime_axis_scaling_axis_product D.replacementAxis

/-- Paper label: `prop:xi-quantile-crt-prime-axis-scaling`. -/
theorem paper_xi_quantile_crt_prime_axis_scaling
    (D : xi_quantile_crt_prime_axis_scaling_data) : D.claim := by
  classical
  have hProduct :
      xi_quantile_crt_prime_axis_scaling_axis_product D.minimalAxis ≤
        xi_quantile_crt_prime_axis_scaling_axis_product D.replacementAxis := by
    simpa [xi_quantile_crt_prime_axis_scaling_axis_product] using
      (Finset.prod_le_prod (s := Finset.univ) (fun i _ => Nat.zero_le (D.minimalAxis i))
        (fun i _ => D.axis_le_replacement i))
  exact le_trans D.minimalAxis_reaches_threshold hProduct

end Omega.Zeta
