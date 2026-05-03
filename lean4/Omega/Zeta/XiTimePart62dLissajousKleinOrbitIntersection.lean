import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- A concrete unit-circle point represented by its real and imaginary coordinates. -/
structure xi_time_part62d_lissajous_klein_orbit_intersection_unitPoint where
  re : ℝ
  im : ℝ
  normSq : re ^ 2 + im ^ 2 = 1

namespace xi_time_part62d_lissajous_klein_orbit_intersection_unitPoint

@[ext]
theorem xi_time_part62d_lissajous_klein_orbit_intersection_ext
    {z w : xi_time_part62d_lissajous_klein_orbit_intersection_unitPoint}
    (hre : z.re = w.re) (him : z.im = w.im) : z = w := by
  cases z
  cases w
  simp_all

end xi_time_part62d_lissajous_klein_orbit_intersection_unitPoint

open xi_time_part62d_lissajous_klein_orbit_intersection_unitPoint

/-- The inverse point on the unit circle. -/
def xi_time_part62d_lissajous_klein_orbit_intersection_inv
    (z : xi_time_part62d_lissajous_klein_orbit_intersection_unitPoint) :
    xi_time_part62d_lissajous_klein_orbit_intersection_unitPoint where
  re := z.re
  im := -z.im
  normSq := by
    simpa [sq] using z.normSq

/-- The trigonometric unit-circle lift of an angle. -/
noncomputable def xi_time_part62d_lissajous_klein_orbit_intersection_circlePoint
    (θ : ℝ) : xi_time_part62d_lissajous_klein_orbit_intersection_unitPoint where
  re := Real.cos θ
  im := Real.sin θ
  normSq := by
    simpa [sq] using Real.cos_sq_add_sin_sq θ

/-- The lifted two-coordinate Lissajous phase point. -/
noncomputable def xi_time_part62d_lissajous_klein_orbit_intersection_lift
    (a b : ℤ) (δ t : ℝ) :
    xi_time_part62d_lissajous_klein_orbit_intersection_unitPoint ×
      xi_time_part62d_lissajous_klein_orbit_intersection_unitPoint :=
  (xi_time_part62d_lissajous_klein_orbit_intersection_circlePoint ((a : ℝ) * t + δ),
    xi_time_part62d_lissajous_klein_orbit_intersection_circlePoint ((b : ℝ) * t))

/-- The real Lissajous projection of the lifted point. -/
noncomputable def xi_time_part62d_lissajous_klein_orbit_intersection_visible
    (a b : ℤ) (δ t : ℝ) : ℝ × ℝ :=
  ((xi_time_part62d_lissajous_klein_orbit_intersection_lift a b δ t).1.re,
    (xi_time_part62d_lissajous_klein_orbit_intersection_lift a b δ t).2.re)

/-- Coordinatewise Klein-four inversion action, with `true` denoting the identity coordinate. -/
def xi_time_part62d_lissajous_klein_orbit_intersection_kleinAction
    (ε : Bool × Bool)
    (z :
      xi_time_part62d_lissajous_klein_orbit_intersection_unitPoint ×
        xi_time_part62d_lissajous_klein_orbit_intersection_unitPoint) :
    xi_time_part62d_lissajous_klein_orbit_intersection_unitPoint ×
      xi_time_part62d_lissajous_klein_orbit_intersection_unitPoint :=
  ((if ε.1 then z.1 else xi_time_part62d_lissajous_klein_orbit_intersection_inv z.1),
    if ε.2 then z.2 else xi_time_part62d_lissajous_klein_orbit_intersection_inv z.2)

/-- Projection from the lifted two-torus to its two real coordinates. -/
def xi_time_part62d_lissajous_klein_orbit_intersection_projection
    (z :
      xi_time_part62d_lissajous_klein_orbit_intersection_unitPoint ×
        xi_time_part62d_lissajous_klein_orbit_intersection_unitPoint) : ℝ × ℝ :=
  (z.1.re, z.2.re)

lemma xi_time_part62d_lissajous_klein_orbit_intersection_eq_or_inv_of_re_eq
    {z w : xi_time_part62d_lissajous_klein_orbit_intersection_unitPoint}
    (h : z.re = w.re) :
    z = w ∨ z = xi_time_part62d_lissajous_klein_orbit_intersection_inv w := by
  have himsq : z.im ^ 2 = w.im ^ 2 := by
    have hz := z.normSq
    have hw := w.normSq
    rw [h] at hz
    nlinarith [hz, hw]
  have hfactor : (z.im - w.im) * (z.im + w.im) = 0 := by
    nlinarith [himsq]
  rcases mul_eq_zero.mp hfactor with hminus | hplus
  · left
    exact xi_time_part62d_lissajous_klein_orbit_intersection_ext h (sub_eq_zero.mp hminus)
  · right
    apply xi_time_part62d_lissajous_klein_orbit_intersection_ext
    · exact h
    · change z.im = -w.im
      linarith

lemma xi_time_part62d_lissajous_klein_orbit_intersection_projection_kleinAction
    (ε : Bool × Bool)
    (z :
      xi_time_part62d_lissajous_klein_orbit_intersection_unitPoint ×
        xi_time_part62d_lissajous_klein_orbit_intersection_unitPoint) :
    xi_time_part62d_lissajous_klein_orbit_intersection_projection
        (xi_time_part62d_lissajous_klein_orbit_intersection_kleinAction ε z) =
      xi_time_part62d_lissajous_klein_orbit_intersection_projection z := by
  rcases ε with ⟨ε₁, ε₂⟩
  cases ε₁ <;> cases ε₂ <;>
    simp [xi_time_part62d_lissajous_klein_orbit_intersection_projection,
      xi_time_part62d_lissajous_klein_orbit_intersection_kleinAction,
      xi_time_part62d_lissajous_klein_orbit_intersection_inv]

/-- Paper-facing statement: equal real projections are exactly coordinatewise Klein inversions,
and identity inversion is excluded by injectivity of the lifted orbit at the two parameters. -/
def xi_time_part62d_lissajous_klein_orbit_intersection_statement : Prop :=
  ∀ (a b : ℤ) (δ t t' : ℝ),
    t ≠ t' →
      (xi_time_part62d_lissajous_klein_orbit_intersection_lift a b δ t =
          xi_time_part62d_lissajous_klein_orbit_intersection_lift a b δ t' → t = t') →
        (xi_time_part62d_lissajous_klein_orbit_intersection_visible a b δ t =
            xi_time_part62d_lissajous_klein_orbit_intersection_visible a b δ t' ↔
          ∃ ε : Bool × Bool,
            ε ≠ (true, true) ∧
              xi_time_part62d_lissajous_klein_orbit_intersection_lift a b δ t =
                xi_time_part62d_lissajous_klein_orbit_intersection_kleinAction ε
                  (xi_time_part62d_lissajous_klein_orbit_intersection_lift a b δ t'))

/-- Paper label: `prop:xi-time-part62d-lissajous-klein-orbit-intersection`. -/
theorem paper_xi_time_part62d_lissajous_klein_orbit_intersection :
    xi_time_part62d_lissajous_klein_orbit_intersection_statement := by
  intro a b δ t t' hne hinj
  constructor
  · intro hvisible
    dsimp [xi_time_part62d_lissajous_klein_orbit_intersection_visible] at hvisible
    have hproj :
        xi_time_part62d_lissajous_klein_orbit_intersection_projection
            (xi_time_part62d_lissajous_klein_orbit_intersection_lift a b δ t) =
          xi_time_part62d_lissajous_klein_orbit_intersection_projection
            (xi_time_part62d_lissajous_klein_orbit_intersection_lift a b δ t') := hvisible
    obtain ⟨h₁, h₂⟩ := Prod.ext_iff.mp hproj
    have hcoord₁ :=
      xi_time_part62d_lissajous_klein_orbit_intersection_eq_or_inv_of_re_eq h₁
    have hcoord₂ :=
      xi_time_part62d_lissajous_klein_orbit_intersection_eq_or_inv_of_re_eq h₂
    rcases hcoord₁ with h₁id | h₁inv <;> rcases hcoord₂ with h₂id | h₂inv
    · exfalso
      apply hne
      apply hinj
      exact Prod.ext h₁id h₂id
    · refine ⟨(true, false), by decide, ?_⟩
      exact Prod.ext h₁id h₂inv
    · refine ⟨(false, true), by decide, ?_⟩
      exact Prod.ext h₁inv h₂id
    · refine ⟨(false, false), by decide, ?_⟩
      exact Prod.ext h₁inv h₂inv
  · rintro ⟨ε, _hneps, horbit⟩
    dsimp [xi_time_part62d_lissajous_klein_orbit_intersection_visible]
    calc
      xi_time_part62d_lissajous_klein_orbit_intersection_projection
          (xi_time_part62d_lissajous_klein_orbit_intersection_lift a b δ t) =
        xi_time_part62d_lissajous_klein_orbit_intersection_projection
          (xi_time_part62d_lissajous_klein_orbit_intersection_kleinAction ε
            (xi_time_part62d_lissajous_klein_orbit_intersection_lift a b δ t')) := by
          rw [horbit]
      _ =
        xi_time_part62d_lissajous_klein_orbit_intersection_projection
          (xi_time_part62d_lissajous_klein_orbit_intersection_lift a b δ t') :=
          xi_time_part62d_lissajous_klein_orbit_intersection_projection_kleinAction ε
            (xi_time_part62d_lissajous_klein_orbit_intersection_lift a b δ t')

end Omega.Zeta
