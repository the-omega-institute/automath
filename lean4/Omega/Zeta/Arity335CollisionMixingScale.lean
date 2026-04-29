import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:arity-335-collision-mixing-scale`. -/
theorem paper_arity_335_collision_mixing_scale (rho lambda : ℝ) (hlambda : 0 < lambda)
    (hrho : 0 < rho) (hrlt : rho < lambda) :
    let ratio := rho / lambda
    0 < ratio ∧ ratio < 1 ∧ 0 < -Real.log ratio ∧
      (let tauMix := 1 / (-Real.log ratio)
       let tHalf := Real.log 2 / (-Real.log ratio)
       tHalf = Real.log 2 * tauMix) := by
  dsimp
  have hratio_pos : 0 < rho / lambda := div_pos hrho hlambda
  have hratio_lt_one : rho / lambda < 1 := (div_lt_one hlambda).2 hrlt
  have hlog_neg : Real.log (rho / lambda) < 0 :=
    Real.log_neg hratio_pos hratio_lt_one
  refine ⟨hratio_pos, hratio_lt_one, ?_, ?_⟩
  · linarith
  · simp [div_eq_mul_inv]

end Omega.Zeta
