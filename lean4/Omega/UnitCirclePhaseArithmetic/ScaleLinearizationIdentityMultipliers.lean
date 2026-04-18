import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- The Cayley right-half-plane coordinate used to linearize the scale action. -/
def scaleHalfPlane (u : ℝ) : ℝ :=
  (1 + u) / (1 - u)

/-- The inverse Cayley transform. -/
def scaleHalfPlaneInv (w : ℝ) : ℝ :=
  (w - 1) / (w + 1)

/-- The Möbius scale map, defined by conjugating multiplication by `1 / m` in half-plane
coordinates. -/
def scalePsi (m u : ℝ) : ℝ :=
  scaleHalfPlaneInv ((1 / m) * scaleHalfPlane u)

/-- The explicit Möbius derivative formula appearing in the paper computation. -/
def scalePsiDerivativeFormula (m u : ℝ) : ℝ :=
  4 * m / (((1 - m) * u + (m + 1)) ^ 2)

lemma scaleHalfPlane_left_inv {w : ℝ} (hw : w + 1 ≠ 0) :
    scaleHalfPlane (scaleHalfPlaneInv w) = w := by
  unfold scaleHalfPlane scaleHalfPlaneInv
  field_simp [hw]
  ring

lemma scaleHalfPlane_scalePsi {m u : ℝ} (_hm : m ≠ 0) (_hu : u ≠ 1)
    (hlin : (1 / m) * scaleHalfPlane u + 1 ≠ 0) :
    scaleHalfPlane (scalePsi m u) = (1 / m) * scaleHalfPlane u := by
  unfold scalePsi
  exact scaleHalfPlane_left_inv hlin

lemma scalePsiDerivativeFormula_one (m : ℝ) :
    scalePsiDerivativeFormula m 1 = m := by
  unfold scalePsiDerivativeFormula
  ring_nf

lemma scalePsiDerivativeFormula_neg_one {m : ℝ} (hm : 0 < m) :
    scalePsiDerivativeFormula m (-1) = 1 / m := by
  unfold scalePsiDerivativeFormula
  field_simp [hm.ne']
  ring

/-- The scale map linearizes to multiplication by `1 / m` in Cayley coordinates, and the explicit
Möbius derivative formula evaluates to the endpoint multipliers `m` and `1 / m`.
    prop:scale-linearization-identity-multipliers -/
theorem paper_scale_linearization_identity_multipliers :
    ∀ ⦃m : ℝ⦄, 0 < m →
      (∀ ⦃u : ℝ⦄, u ≠ 1 → (1 / m) * scaleHalfPlane u + 1 ≠ 0 →
        scaleHalfPlane (scalePsi m u) = (1 / m) * scaleHalfPlane u) ∧
      scalePsiDerivativeFormula m 1 = m ∧
      scalePsiDerivativeFormula m (-1) = 1 / m := by
  intro m hm
  refine ⟨?_, scalePsiDerivativeFormula_one m, scalePsiDerivativeFormula_neg_one hm⟩
  intro u hu hlin
  exact scaleHalfPlane_scalePsi hm.ne' hu hlin

end

end Omega.UnitCirclePhaseArithmetic
