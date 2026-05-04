import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete affine fixed-point data for a positive-layer cocycle model over integers. -/
structure xi_time_part9g_affine_fixed_point_cocycle_bundle where
  shift : ℤ → ℤ → ℤ
  eval : ℤ → ℤ
  fixedPoint : ℤ → ℤ
  product : ℤ → ℤ → ℤ
  product_law : ∀ g h, product g h = g + h
  eval_additive : ∀ g h, eval (g + h) = eval g + shift g (eval h)
  fixed_point_equation : ∀ g, fixedPoint g = eval g

/-- Public target type for the affine fixed-point cocycle theorem. -/
abbrev xi_time_part9g_affine_fixed_point_cocycle_data :=
  xi_time_part9g_affine_fixed_point_cocycle_bundle

/-- The affine fixed-point map is a one-cocycle for the semidirect product law. -/
def xi_time_part9g_affine_fixed_point_cocycle_data.claim
    (D : xi_time_part9g_affine_fixed_point_cocycle_data) : Prop :=
  ∀ g h, D.fixedPoint (D.product g h) = D.fixedPoint g + D.shift g (D.fixedPoint h)

/-- Paper label: `thm:xi-time-part9g-affine-fixed-point-cocycle`. -/
theorem paper_xi_time_part9g_affine_fixed_point_cocycle
    (D : xi_time_part9g_affine_fixed_point_cocycle_data) :
    xi_time_part9g_affine_fixed_point_cocycle_data.claim D := by
  intro g h
  calc
    D.fixedPoint (D.product g h) = D.eval (D.product g h) := D.fixed_point_equation _
    _ = D.eval (g + h) := by rw [D.product_law g h]
    _ = D.eval g + D.shift g (D.eval h) := D.eval_additive g h
    _ = D.fixedPoint g + D.shift g (D.fixedPoint h) := by
      rw [← D.fixed_point_equation g, ← D.fixed_point_equation h]

end Omega.Zeta
