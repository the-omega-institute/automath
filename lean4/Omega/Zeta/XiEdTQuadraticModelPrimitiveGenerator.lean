import Mathlib.Tactic
import Omega.Zeta.XiEdInftyFiberHalvingTangentIntegral

namespace Omega.Zeta

/-- The `t`-coordinate attached to the primitive-generator model. -/
def xi_ed_t_quadratic_model_primitive_generator_t_coord (m u : ℚ) : ℚ :=
  (u - 1) / (u - xiEdInftyFiberTangentLine m)

/-- The quadratic-generator numerator `W = ((t - 1)^2 m + 8 t^2) / 2`. -/
def xi_ed_t_quadratic_model_primitive_generator_W (m u : ℚ) : ℚ :=
  let t := xi_ed_t_quadratic_model_primitive_generator_t_coord m u
  (((t - 1) ^ 2) * m + 8 * t ^ 2) / 2

/-- The quadratic relation in `m` obtained after eliminating `u`. -/
def xi_ed_t_quadratic_model_primitive_generator_quadratic_relation (m u : ℚ) : Prop :=
  let t := xi_ed_t_quadratic_model_primitive_generator_t_coord m u
  (t - 1) ^ 2 * m ^ 2 + 16 * t ^ 2 * m + 64 * t ^ 2 + 4 * t - 4 = 0

/-- The cubic Weierstrass relation induced by the discriminant of the quadratic `m`-relation. -/
def xi_ed_t_quadratic_model_primitive_generator_weierstrass_relation (m u : ℚ) : Prop :=
  let t := xi_ed_t_quadratic_model_primitive_generator_t_coord m u
  let W := xi_ed_t_quadratic_model_primitive_generator_W m u
  W ^ 2 = 31 * t ^ 3 - 13 * t ^ 2 - 3 * t + 1

lemma xi_ed_t_quadratic_model_primitive_generator_quadratic_identity {m u : ℚ}
    (hden : u - xiEdInftyFiberTangentLine m ≠ 0) :
    let t := xi_ed_t_quadratic_model_primitive_generator_t_coord m u
    (t - 1) ^ 2 * m ^ 2 + 16 * t ^ 2 * m + 64 * t ^ 2 + 4 * t - 4 =
      16 * (m + 4) * (u ^ 2 - xiEdInftyFiberCubic m) / (u - xiEdInftyFiberTangentLine m) ^ 2 := by
  dsimp [xi_ed_t_quadratic_model_primitive_generator_t_coord]
  field_simp [hden]
  unfold xiEdInftyFiberTangentLine xiEdInftyFiberCubic
  ring_nf

lemma xi_ed_t_quadratic_model_primitive_generator_weierstrass_identity {m u : ℚ}
    (hden : u - xiEdInftyFiberTangentLine m ≠ 0) :
    let t := xi_ed_t_quadratic_model_primitive_generator_t_coord m u
    let W := xi_ed_t_quadratic_model_primitive_generator_W m u
    W ^ 2 - (31 * t ^ 3 - 13 * t ^ 2 - 3 * t + 1) =
      256 * (m + 4) ^ 3 * (u ^ 2 - xiEdInftyFiberCubic m) /
        (u - xiEdInftyFiberTangentLine m) ^ 4 := by
  dsimp [xi_ed_t_quadratic_model_primitive_generator_t_coord,
    xi_ed_t_quadratic_model_primitive_generator_W]
  field_simp [hden]
  unfold xiEdInftyFiberTangentLine xiEdInftyFiberCubic
  ring_nf

/-- Paper label: `thm:xi-ed-t-quadratic-model-primitive-generator`. Eliminating `u` from
`t (u - 8m - 33) = u - 1` over the affine model `u^2 = -4 m^3 - 16 m^2 + 16 m + 65` gives the
quadratic relation in `m`, and the corresponding discriminant identity yields the cubic
Weierstrass equation for `W`. -/
theorem paper_xi_ed_t_quadratic_model_primitive_generator {m u : ℚ}
    (hcurve : xiEdInftyFiberOnCurve m u) (hden : u - xiEdInftyFiberTangentLine m ≠ 0) :
    xi_ed_t_quadratic_model_primitive_generator_quadratic_relation m u ∧
      xi_ed_t_quadratic_model_primitive_generator_weierstrass_relation m u := by
  let hhalving := paper_xi_ed_infty_fiber_halving_tangent_integral
  have _htangent : xiEdInftyFiberTangentLine m = 8 * m + 33 := hhalving.tangentLineClosedForm m
  have hquad :=
    xi_ed_t_quadratic_model_primitive_generator_quadratic_identity (m := m) (u := u) hden
  have hwei :=
    xi_ed_t_quadratic_model_primitive_generator_weierstrass_identity (m := m) (u := u) hden
  have hcubic : u ^ 2 - xiEdInftyFiberCubic m = 0 := by
    simpa [xiEdInftyFiberOnCurve] using sub_eq_zero.mpr hcurve
  constructor
  · dsimp [xi_ed_t_quadratic_model_primitive_generator_quadratic_relation] at hquad ⊢
    rw [hquad, hcubic]
    ring
  · have hrhs_zero :
        256 * (m + 4) ^ 3 * (u ^ 2 - xiEdInftyFiberCubic m) /
            (u - xiEdInftyFiberTangentLine m) ^ 4 =
          0 := by
      rw [hcubic]
      ring
    dsimp [xi_ed_t_quadratic_model_primitive_generator_weierstrass_relation] at hwei ⊢
    rw [hrhs_zero] at hwei
    linarith

end Omega.Zeta
