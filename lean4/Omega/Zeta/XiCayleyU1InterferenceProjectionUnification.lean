import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Half-angle coordinate used by the Cayley parametrization. -/
def xi_cayley_u1_interference_projection_unification_half_angle (t : ℝ) : ℝ :=
  2 * Real.arctan t

/-- The unitary Cayley phase written in half-angle form. -/
def xi_cayley_u1_interference_projection_unification_phase (t : ℝ) : ℂ :=
  ((Real.cos (xi_cayley_u1_interference_projection_unification_half_angle t) : ℝ) : ℂ) +
    Complex.I *
      ((Real.sin (xi_cayley_u1_interference_projection_unification_half_angle t) : ℝ) : ℂ)

/-- The `m`-th U(1) orbit phase with an added real phase shift. -/
def xi_cayley_u1_interference_projection_unification_orbit_phase
    (m : ℕ) (δ t : ℝ) : ℂ :=
  ((Real.cos ((m : ℝ) * xi_cayley_u1_interference_projection_unification_half_angle t + δ) :
      ℝ) : ℂ) +
    Complex.I *
      ((Real.sin ((m : ℝ) * xi_cayley_u1_interference_projection_unification_half_angle t + δ) :
        ℝ) : ℂ)

/-- First real projection of the shifted U(1) orbit. -/
def xi_cayley_u1_interference_projection_unification_X (m : ℕ) (δ t : ℝ) : ℝ :=
  Real.cos ((m : ℝ) * xi_cayley_u1_interference_projection_unification_half_angle t + δ)

/-- Second real projection of the unshifted U(1) orbit. -/
def xi_cayley_u1_interference_projection_unification_Y (m : ℕ) (t : ℝ) : ℝ :=
  Real.cos ((m : ℝ) * xi_cayley_u1_interference_projection_unification_half_angle t)

/-- The cosine-coordinate Lissajous pair read out from two real projections. -/
def xi_cayley_u1_interference_projection_unification_lissajous_pair
    (a b : ℕ) (δ t : ℝ) : ℝ × ℝ :=
  (xi_cayley_u1_interference_projection_unification_X a δ t,
    xi_cayley_u1_interference_projection_unification_Y b t)

/-- The complex interference projection of two U(1) powers. -/
def xi_cayley_u1_interference_projection_unification_interference
    (p q : ℕ) (t : ℝ) : ℂ :=
  (xi_cayley_u1_interference_projection_unification_phase t ^ p +
      xi_cayley_u1_interference_projection_unification_phase t ^ q) / 2

/-- The rose-family readout as the same complex interference projection. -/
def xi_cayley_u1_interference_projection_unification_rose
    (n d : ℕ) (t : ℝ) : ℂ :=
  xi_cayley_u1_interference_projection_unification_interference (d + n) (d - n) t

/-- Concrete statement packaging the Cayley half-angle identity, the two real projections, and
the U(1)-orbit interference projection. -/
def xi_cayley_u1_interference_projection_unification_statement : Prop :=
  (∀ t : ℝ,
      xi_cayley_u1_interference_projection_unification_phase t =
        ((Real.cos (2 * Real.arctan t) : ℝ) : ℂ) +
          Complex.I * ((Real.sin (2 * Real.arctan t) : ℝ) : ℂ)) ∧
    (∀ (m : ℕ) (δ t : ℝ),
      xi_cayley_u1_interference_projection_unification_X m δ t =
        Real.cos
          ((m : ℝ) * xi_cayley_u1_interference_projection_unification_half_angle t + δ)) ∧
    (∀ (m : ℕ) (t : ℝ),
      xi_cayley_u1_interference_projection_unification_Y m t =
        Real.cos ((m : ℝ) * xi_cayley_u1_interference_projection_unification_half_angle t)) ∧
    (∀ (a b : ℕ) (δ t : ℝ),
      xi_cayley_u1_interference_projection_unification_lissajous_pair a b δ t =
        (Real.cos
            ((a : ℝ) * xi_cayley_u1_interference_projection_unification_half_angle t + δ),
          Real.cos
            ((b : ℝ) * xi_cayley_u1_interference_projection_unification_half_angle t))) ∧
    (∀ (n d : ℕ) (t : ℝ),
      xi_cayley_u1_interference_projection_unification_rose n d t =
        xi_cayley_u1_interference_projection_unification_interference (d + n) (d - n) t)

/-- Paper label: `cor:xi-cayley-u1-interference-projection-unification`. -/
theorem paper_xi_cayley_u1_interference_projection_unification :
    xi_cayley_u1_interference_projection_unification_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t
    simp [xi_cayley_u1_interference_projection_unification_phase,
      xi_cayley_u1_interference_projection_unification_half_angle]
  · intro m δ t
    rfl
  · intro m t
    rfl
  · intro a b δ t
    simp [xi_cayley_u1_interference_projection_unification_lissajous_pair,
      xi_cayley_u1_interference_projection_unification_X,
      xi_cayley_u1_interference_projection_unification_Y]
  · intro n d t
    rfl

end

end Omega.Zeta
