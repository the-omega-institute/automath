import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The prefixed Cayley phase numerator `(1 + i t)^(2m)`. -/
def xi_cayley_phase_double_rotation_rational_parity_numerator (m : ℕ) (t : ℝ) : ℂ :=
  ((1 : ℂ) + Complex.I * (t : ℂ)) ^ (2 * m)

/-- The real numerator in the Cayley phase closed form. -/
def xi_cayley_phase_double_rotation_rational_parity_P (m : ℕ) (t : ℝ) : ℝ :=
  (xi_cayley_phase_double_rotation_rational_parity_numerator m t).re

/-- The imaginary numerator in the Cayley phase closed form. -/
def xi_cayley_phase_double_rotation_rational_parity_Q (m : ℕ) (t : ℝ) : ℝ :=
  (xi_cayley_phase_double_rotation_rational_parity_numerator m t).im

/-- The denominator `(1+t^2)^m` appearing after Cayley rationalization. -/
def xi_cayley_phase_double_rotation_rational_parity_denominator (m : ℕ) (t : ℝ) : ℝ :=
  (1 + t ^ 2) ^ m

/-- The rationalized Cayley phase power. -/
def xi_cayley_phase_double_rotation_rational_parity_phase (m : ℕ) (t : ℝ) : ℂ :=
  ((xi_cayley_phase_double_rotation_rational_parity_P m t : ℂ) +
      Complex.I * (xi_cayley_phase_double_rotation_rational_parity_Q m t : ℂ)) /
    (xi_cayley_phase_double_rotation_rational_parity_denominator m t : ℂ)

/-- The double-rotation interference average, expressed with the common prefixed phase map. -/
def xi_cayley_phase_double_rotation_rational_parity_interference_orbit
    (p q : ℕ) (t : ℝ) : ℂ :=
  (xi_cayley_phase_double_rotation_rational_parity_phase p t +
      xi_cayley_phase_double_rotation_rational_parity_phase q t) / 2

/-- Closed form: the phase numerator is exactly its real plus imaginary decomposition. -/
def xi_cayley_phase_double_rotation_rational_parity_closed_form : Prop :=
  ∀ (m : ℕ) (t : ℝ),
    xi_cayley_phase_double_rotation_rational_parity_phase m t =
      xi_cayley_phase_double_rotation_rational_parity_numerator m t /
        (xi_cayley_phase_double_rotation_rational_parity_denominator m t : ℂ)

/-- Parity: the rationalized numerator has even real part and odd imaginary part. -/
def xi_cayley_phase_double_rotation_rational_parity_parity : Prop :=
  ∀ (m : ℕ) (t : ℝ),
    xi_cayley_phase_double_rotation_rational_parity_P m (-t) =
        xi_cayley_phase_double_rotation_rational_parity_P m t ∧
      xi_cayley_phase_double_rotation_rational_parity_Q m (-t) =
        -xi_cayley_phase_double_rotation_rational_parity_Q m t

/-- Interference is built by averaging the two rationalized rotations. -/
def xi_cayley_phase_double_rotation_rational_parity_interference : Prop :=
  ∀ (p q : ℕ) (t : ℝ),
    xi_cayley_phase_double_rotation_rational_parity_interference_orbit p q t =
      (xi_cayley_phase_double_rotation_rational_parity_phase p t +
          xi_cayley_phase_double_rotation_rational_parity_phase q t) / 2

private lemma xi_cayley_phase_double_rotation_rational_parity_closed_form_proof :
    xi_cayley_phase_double_rotation_rational_parity_closed_form := by
  intro m t
  unfold xi_cayley_phase_double_rotation_rational_parity_phase
    xi_cayley_phase_double_rotation_rational_parity_P
    xi_cayley_phase_double_rotation_rational_parity_Q
  rw [mul_comm Complex.I
    (xi_cayley_phase_double_rotation_rational_parity_numerator m t).im]
  rw [Complex.re_add_im]

private lemma xi_cayley_phase_double_rotation_rational_parity_conj_numerator
    (m : ℕ) (t : ℝ) :
    xi_cayley_phase_double_rotation_rational_parity_numerator m (-t) =
      star (xi_cayley_phase_double_rotation_rational_parity_numerator m t) := by
  unfold xi_cayley_phase_double_rotation_rational_parity_numerator
  rw [star_pow]
  congr 1
  simp [mul_comm]

private lemma xi_cayley_phase_double_rotation_rational_parity_parity_proof :
    xi_cayley_phase_double_rotation_rational_parity_parity := by
  intro m t
  have h := xi_cayley_phase_double_rotation_rational_parity_conj_numerator m t
  constructor
  · unfold xi_cayley_phase_double_rotation_rational_parity_P
    rw [h]
    simp
  · unfold xi_cayley_phase_double_rotation_rational_parity_Q
    rw [h]
    simp

private lemma xi_cayley_phase_double_rotation_rational_parity_interference_proof :
    xi_cayley_phase_double_rotation_rational_parity_interference := by
  intro p q t
  rfl

/-- Paper label: `thm:xi-cayley-phase-double-rotation-rational-parity`. -/
theorem paper_xi_cayley_phase_double_rotation_rational_parity :
    xi_cayley_phase_double_rotation_rational_parity_closed_form ∧
      xi_cayley_phase_double_rotation_rational_parity_parity ∧
      xi_cayley_phase_double_rotation_rational_parity_interference := by
  exact ⟨xi_cayley_phase_double_rotation_rational_parity_closed_form_proof,
    xi_cayley_phase_double_rotation_rational_parity_parity_proof,
    xi_cayley_phase_double_rotation_rational_parity_interference_proof⟩

end

end Omega.Zeta
