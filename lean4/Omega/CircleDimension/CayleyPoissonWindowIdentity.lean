import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

open scoped BigOperators
open Real intervalIntegral

/-- The Cayley-modulus Poisson window identity reduces to the logarithmic antiderivative of
`s / (γ^2 + s^2)` over the symmetric window `[λ - δ, λ + δ]`.
    prop:cdim-cayley-poisson-window-identity -/
theorem paper_cdim_cayley_poisson_window_identity (gamma lam delta : Real) (hlam : 0 < lam)
    (hdelta : 0 < delta) (hlt : delta < lam) :
    (1 / 2) *
        Real.log ((gamma^2 + (lam + delta)^2) / (gamma^2 + (lam - delta)^2)) =
      ∫ s in lam - delta..lam + delta, s / (gamma^2 + s^2) := by
  let a : Real := lam - delta
  let b : Real := lam + delta
  have ha : 0 < a := by
    dsimp [a]
    exact sub_pos.2 hlt
  have hb : 0 < b := by
    dsimp [b]
    exact add_pos hlam hdelta
  have hab : a ≤ b := by
    dsimp [a, b]
    linarith
  have hfa : 0 < gamma^2 + a^2 := by
    exact add_pos_of_nonneg_of_pos (sq_nonneg gamma) (sq_pos_of_pos ha)
  have hfb : 0 < gamma^2 + b^2 := by
    exact add_pos_of_nonneg_of_pos (sq_nonneg gamma) (sq_pos_of_pos hb)
  have hsub :
      ∫ s in a..b, ((fun u : Real => 1 / u) ∘ fun x : Real => gamma^2 + x^2) s * (2 * s) =
        ∫ u in gamma^2 + a^2..gamma^2 + b^2, 1 / u := by
    refine intervalIntegral.integral_comp_mul_deriv' ?_ ?_ ?_
    · intro x hx
      simpa [pow_two, two_mul, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
        mul_assoc] using (hasDerivAt_pow 2 x).const_add (gamma^2)
    · simpa [two_mul] using (continuous_const.mul continuous_id).continuousOn
    · simpa [one_div] using
        ((continuousOn_id :
            ContinuousOn (fun y : Real => y) ((fun x : Real => gamma^2 + x^2) '' Set.uIcc a b)).inv₀
          <| by
            intro y hy
            rcases hy with ⟨x, hx, rfl⟩
            rw [Set.uIcc_of_le hab] at hx
            have hx_pos : 0 < x := lt_of_lt_of_le ha hx.1
            exact (add_pos_of_nonneg_of_pos (sq_nonneg gamma) (sq_pos_of_pos hx_pos)).ne')
  have hlog :
      ∫ s in a..b, ((fun u : Real => 1 / u) ∘ fun x : Real => gamma^2 + x^2) s * (2 * s) =
        Real.log ((gamma^2 + b^2) / (gamma^2 + a^2)) := by
    rw [hsub, integral_one_div_of_pos hfa hfb]
  have hmain :
      (2 : Real) * (∫ s in a..b, s / (gamma^2 + s^2)) =
        Real.log ((gamma^2 + b^2) / (gamma^2 + a^2)) := by
    calc
      (2 : Real) * (∫ s in a..b, s / (gamma^2 + s^2)) =
          ∫ s in a..b, 2 * (s / (gamma^2 + s^2)) := by
            rw [intervalIntegral.integral_const_mul]
      _ = ∫ s in a..b,
            ((fun u : Real => 1 / u) ∘ fun x : Real => gamma^2 + x^2) s * (2 * s) := by
            refine intervalIntegral.integral_congr_ae <| Filter.Eventually.of_forall ?_
            intro s
            simp [Function.comp, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      _ = Real.log ((gamma^2 + b^2) / (gamma^2 + a^2)) := hlog
  have hhalf := congrArg (fun t : Real => (1 / 2) * t) hmain
  simpa [a, b, mul_assoc, mul_left_comm, mul_comm] using hhalf.symm

end Omega.CircleDimension
