import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

namespace Omega.Zeta

open Filter
open scoped Topology

/-- The symmetric shadowing window around the approximate zero `tm`. -/
def xiShadowWindow (tm r : ℝ) : Set ℝ :=
  Set.Icc (tm - r) (tm + r)

/-- A continuous strictly monotone function with a sign change on a symmetric window has a unique
zero there. If the function also has a quantitative slope lower bound away from the center `tm`,
then every true zero is explicitly localized, and any recursively shadowed sequence whose window
radii shrink to `0` converges back to `tm`.
    thm:xi-recursive-zero-shadowing-explicit -/
theorem paper_xi_recursive_zero_shadowing_explicit
    (f : ℝ → ℝ) (tm r ε μ : ℝ)
    (hr : 0 < r) (hμ : 0 < μ)
    (hcont : ContinuousOn f (xiShadowWindow tm r))
    (hmono : StrictMonoOn f (xiShadowWindow tm r))
    (hleft : f (tm - r) ≤ 0) (hright : 0 ≤ f (tm + r))
    (htm : |f tm| ≤ ε)
    (hslope : ∀ x ∈ xiShadowWindow tm r, μ * |x - tm| ≤ |f x - f tm|) :
    (∃! x, x ∈ xiShadowWindow tm r ∧ f x = 0) ∧
      (∀ x, x ∈ xiShadowWindow tm r → f x = 0 → |x - tm| ≤ ε / μ) ∧
      (∀ s ρ : ℕ → ℝ, (∀ n, 0 ≤ ρ n) → Tendsto ρ atTop (𝓝 0) →
        (∀ n, |s n - tm| ≤ ρ n) → Tendsto s atTop (𝓝 tm)) := by
  have hwindow_nonempty : tm - r ≤ tm + r := by linarith
  have hzero_mem :
      (0 : ℝ) ∈ f '' xiShadowWindow tm r := by
    have hIVT :=
      intermediate_value_Icc hwindow_nonempty hcont ⟨hleft, hright⟩
    simpa [xiShadowWindow] using hIVT
  rcases hzero_mem with ⟨x0, hx0mem, hx0zero⟩
  have huniq : ∀ y, y ∈ xiShadowWindow tm r → f y = 0 → y = x0 := by
    intro y hymem hyzero
    have hxy : x0 = y := by
      apply hmono.injOn hx0mem hymem
      simpa [hx0zero, hyzero]
    exact hxy.symm
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨x0, ⟨hx0mem, hx0zero⟩, ?_⟩
    intro y hy
    exact huniq y hy.1 hy.2
  · intro x hxmem hxzero
    have hslope' : μ * |x - tm| ≤ |f x - f tm| := hslope x hxmem
    have hrewrite : |f x - f tm| = |f tm| := by
      simpa [hxzero, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, abs_sub_comm]
    have hbound : μ * |x - tm| ≤ ε := by
      calc
        μ * |x - tm| ≤ |f x - f tm| := hslope'
        _ = |f tm| := hrewrite
        _ ≤ ε := htm
    exact (le_div_iff₀ hμ).2 (by simpa [mul_comm] using hbound)
  · intro s ρ hρnn hρlim hshadow
    refine tendsto_iff_dist_tendsto_zero.2 ?_
    have hdist :
        Tendsto (fun n : ℕ => |s n - tm|) atTop (𝓝 0) := by
      refine squeeze_zero (fun n => abs_nonneg _) (fun n => hshadow n) hρlim
    simpa [Real.dist_eq] using hdist

end Omega.Zeta
