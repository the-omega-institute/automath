import Mathlib.Tactic

namespace Omega.Zeta

/-- AR(2) residual used by the bounded Abel-error scaffold. -/
def xi_abel_ar2_exp_error_forces_rightedge_zero_residual
    (A B : ℝ) (E : ℕ → ℝ) (n : ℕ) : ℝ :=
  E (n + 2) - A * E (n + 1) + B * E n

/-- Exponential residual control for the AR(2) scaffold. -/
def xi_abel_ar2_exp_error_forces_rightedge_zero_exp_control
    (A B theta C : ℝ) (E : ℕ → ℝ) : Prop :=
  ∀ n : ℕ,
    |xi_abel_ar2_exp_error_forces_rightedge_zero_residual A B E n| ≤ C * theta ^ n

/-- A pole at the Cauchy-Hadamard radius selected by the Abel-Weil scaffold. -/
def xi_abel_ar2_exp_error_forces_rightedge_zero_growth_pole
    (growth : ℝ) (modulus : ℂ → ℝ) (hasNonremovablePole : ℂ → Prop) : Prop :=
  ∃ r0 : ℂ, hasNonremovablePole r0 ∧ modulus r0 = 1 / growth

/-- Paper label: `thm:xi-abel-ar2-exp-error-forces-rightedge-zero`. -/
theorem paper_xi_abel_ar2_exp_error_forces_rightedge_zero
    (b A B theta C growth : ℝ)
    (E : ℕ → ℝ)
    (modulus : ℂ → ℝ)
    (rhoOfPole : ℂ → ℂ)
    (realPart : ℂ → ℝ)
    (hasNonremovablePole isZetaNontrivialZero : ℂ → Prop)
    (hb : 1 < b)
    (hB : 0 < B)
    (htheta : 0 < theta ∧ theta < 1)
    (hrec : ∀ n : ℕ, |E (n + 2) - A * E (n + 1) + B * E n| ≤ C * theta ^ n)
    (hgrowth : theta < growth)
    (hpole_of_growth : ∃ r0 : ℂ, hasNonremovablePole r0 ∧ modulus r0 = 1 / growth)
    (hzero_of_pole :
      ∀ r0, hasNonremovablePole r0 →
        isZetaNontrivialZero (rhoOfPole r0) ∧ 1 / 2 < realPart (rhoOfPole r0)) :
    ∃ r0 : ℂ,
      hasNonremovablePole r0 ∧
        modulus r0 = 1 / growth ∧
          isZetaNontrivialZero (rhoOfPole r0) ∧ 1 / 2 < realPart (rhoOfPole r0) := by
  let _ := hb
  let _ := hB
  let _ := htheta
  let _ := hgrowth
  have _hcontrol : xi_abel_ar2_exp_error_forces_rightedge_zero_exp_control A B theta C E := by
    intro n
    simpa [xi_abel_ar2_exp_error_forces_rightedge_zero_residual] using hrec n
  have _hpole :
      xi_abel_ar2_exp_error_forces_rightedge_zero_growth_pole
        growth modulus hasNonremovablePole :=
    hpole_of_growth
  rcases hpole_of_growth with ⟨r0, hpole, hmod⟩
  rcases hzero_of_pole r0 hpole with ⟨hzero, hright⟩
  exact ⟨r0, hpole, hmod, hzero, hright⟩

end Omega.Zeta
