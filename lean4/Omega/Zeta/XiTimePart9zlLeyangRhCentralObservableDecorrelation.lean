import Mathlib

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `thm:xi-time-part9zl-leyang-rh-central-observable-decorrelation`. -/
theorem paper_xi_time_part9zl_leyang_rh_central_observable_decorrelation
    {G H : Type*} [Fintype G] [Fintype H] (f : G → ℂ) (g : H → ℂ)
    (jointLimit : G → H → ℂ)
    (hprod : ∀ a b,
      jointLimit a b = (Fintype.card G : ℂ)⁻¹ * (Fintype.card H : ℂ)⁻¹) :
    (∑ a, ∑ b, f a * g b * jointLimit a b) =
      ((Fintype.card G : ℂ)⁻¹ * ∑ a, f a) *
        ((Fintype.card H : ℂ)⁻¹ * ∑ b, g b) := by
  let cG : ℂ := (Fintype.card G : ℂ)⁻¹
  let cH : ℂ := (Fintype.card H : ℂ)⁻¹
  calc
    (∑ a, ∑ b, f a * g b * jointLimit a b) =
        ∑ a, ∑ b, (cG * f a) * (cH * g b) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [hprod a b]
      ring
    _ = (∑ a, cG * f a) * (∑ b, cH * g b) := by
      exact (Fintype.sum_mul_sum (fun a => cG * f a) (fun b => cH * g b)).symm
    _ = ((Fintype.card G : ℂ)⁻¹ * ∑ a, f a) *
        ((Fintype.card H : ℂ)⁻¹ * ∑ b, g b) := by
      simp [cG, cH, Finset.mul_sum]

end Omega.Zeta
