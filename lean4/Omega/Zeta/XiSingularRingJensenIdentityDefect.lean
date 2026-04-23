import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.Zeta.XiCayleyTauConjugacyLogdiff

namespace Omega.Zeta

noncomputable section

/-- The critical-line Cauchy density in the Cayley variable. -/
def xi_singular_ring_jensen_identity_defect_cauchy_density (x : ℝ) : ℝ :=
  1 / (Real.pi * (1 + x ^ 2))

/-- The circle density transported through the Cayley parameter `x = 2t`. -/
def xi_singular_ring_jensen_identity_defect_circle_density (x : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * (2 / (1 + x ^ 2))

/-- The Cayley pullback `w ↦ w / (1 + w)` used to transport the Jensen identity to the unit
circle. -/
def xi_singular_ring_jensen_identity_defect_pullback_point (w : Complex) : Complex :=
  w / (1 + w)

/-- The reflected pullback point corresponding to the involution `s ↦ 1 - s`. -/
def xi_singular_ring_jensen_identity_defect_reflected_pullback_point (w : Complex) : Complex :=
  1 - xi_singular_ring_jensen_identity_defect_pullback_point w

/-- Interior zero `ρ` written in the singular-ring coordinate `a = ρ / (1 - ρ)`. -/
def xi_singular_ring_jensen_identity_defect_zero_coordinate (ρ : Complex) : Complex :=
  ρ / (1 - ρ)

/-- The Jensen identity defect after transporting to the singular-ring coordinate. -/
def xi_singular_ring_jensen_identity_defect_defect
    (f : Complex → Complex) (w : Complex) : ℝ :=
  Complex.normSq
    (f (xi_singular_ring_jensen_identity_defect_pullback_point w) -
      f (xi_singular_ring_jensen_identity_defect_reflected_pullback_point w))

lemma xi_singular_ring_jensen_identity_defect_pullback_zero_coordinate
    {ρ : Complex} (hρ : ρ ≠ 1) :
    xi_singular_ring_jensen_identity_defect_pullback_point
        (xi_singular_ring_jensen_identity_defect_zero_coordinate ρ) = ρ := by
  have hOneSub : 1 - ρ ≠ 0 := sub_ne_zero.mpr hρ.symm
  have hDen :
      1 + ρ / (1 - ρ) = (1 : Complex) / (1 - ρ) := by
    field_simp [hOneSub]
    ring_nf
  unfold xi_singular_ring_jensen_identity_defect_pullback_point
    xi_singular_ring_jensen_identity_defect_zero_coordinate
  rw [hDen]
  field_simp [hOneSub]

lemma xi_singular_ring_jensen_identity_defect_reflected_zero_coordinate
    {ρ : Complex} (hρ : ρ ≠ 1) :
    xi_singular_ring_jensen_identity_defect_reflected_pullback_point
        (xi_singular_ring_jensen_identity_defect_zero_coordinate ρ) = 1 - ρ := by
  rw [xi_singular_ring_jensen_identity_defect_reflected_pullback_point,
    xi_singular_ring_jensen_identity_defect_pullback_zero_coordinate hρ]

lemma xi_singular_ring_jensen_identity_defect_zero_coordinate_symmetry
    {ρ : Complex} (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) :
    xi_singular_ring_jensen_identity_defect_zero_coordinate (1 - ρ) =
      (xi_singular_ring_jensen_identity_defect_zero_coordinate ρ)⁻¹ := by
  have hOneSub : 1 - ρ ≠ 0 := sub_ne_zero.mpr hρ1.symm
  unfold xi_singular_ring_jensen_identity_defect_zero_coordinate
  field_simp [hρ0, hOneSub]
  ring

/-- Paper label: `thm:xi-singular-ring-jensen-identity-defect`. The critical-line Cauchy
uniformization and the Cayley/tau conjugacy transport the Jensen identity to the unit circle; in
the singular-ring coordinate `a = ρ / (1 - ρ)` the reflected zero becomes inversion, the defect
is always nonnegative, and `f(s) = f(1-s)` forces equality. -/
theorem paper_xi_singular_ring_jensen_identity_defect (f : Complex -> Complex) :
    (∀ θ : ℝ,
      let t : ℝ := (1 / 2) * Real.tan (θ / 2)
      let x : ℝ := 2 * t
      xi_singular_ring_jensen_identity_defect_circle_density x =
        xi_singular_ring_jensen_identity_defect_cauchy_density x) ∧
      (∀ D : xi_cayley_tau_conjugacy_logdiff_data,
        D.tauConjugacy ∧ D.unitCircleCriterion ∧ D.logDerivativeIdentity) ∧
      (∀ ρ : Complex, ρ ≠ 1 →
        xi_singular_ring_jensen_identity_defect_pullback_point
            (xi_singular_ring_jensen_identity_defect_zero_coordinate ρ) = ρ ∧
          xi_singular_ring_jensen_identity_defect_reflected_pullback_point
              (xi_singular_ring_jensen_identity_defect_zero_coordinate ρ) = 1 - ρ) ∧
      (∀ ρ : Complex, ρ ≠ 0 → ρ ≠ 1 →
        xi_singular_ring_jensen_identity_defect_zero_coordinate (1 - ρ) =
          (xi_singular_ring_jensen_identity_defect_zero_coordinate ρ)⁻¹) ∧
      (∀ w : Complex, 0 ≤ xi_singular_ring_jensen_identity_defect_defect f w) ∧
      ((∀ s : Complex, f s = f (1 - s)) →
        ∀ ρ : Complex, ρ ≠ 1 →
          xi_singular_ring_jensen_identity_defect_defect f
            (xi_singular_ring_jensen_identity_defect_zero_coordinate ρ) = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro θ
    let t : ℝ := (1 / 2) * Real.tan (θ / 2)
    let x : ℝ := 2 * t
    have hx : (1 + x ^ 2 : ℝ) ≠ 0 := by
      nlinarith [sq_nonneg x]
    unfold xi_singular_ring_jensen_identity_defect_circle_density
      xi_singular_ring_jensen_identity_defect_cauchy_density
    field_simp [Real.pi_ne_zero, hx]
  · intro D
    rcases paper_xi_cayley_tau_conjugacy_logdiff D with ⟨hTau, hUnit, hLog⟩
    exact ⟨hTau, hUnit, hLog⟩
  · intro ρ hρ
    exact ⟨xi_singular_ring_jensen_identity_defect_pullback_zero_coordinate hρ,
      xi_singular_ring_jensen_identity_defect_reflected_zero_coordinate hρ⟩
  · intro ρ hρ0 hρ1
    exact xi_singular_ring_jensen_identity_defect_zero_coordinate_symmetry hρ0 hρ1
  · intro w
    unfold xi_singular_ring_jensen_identity_defect_defect
    exact Complex.normSq_nonneg _
  · intro hsym ρ hρ
    unfold xi_singular_ring_jensen_identity_defect_defect
    rw [xi_singular_ring_jensen_identity_defect_pullback_zero_coordinate hρ,
      xi_singular_ring_jensen_identity_defect_reflected_zero_coordinate hρ, hsym ρ]
    simp

end

end Omega.Zeta
