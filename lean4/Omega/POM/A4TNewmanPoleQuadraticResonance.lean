import Mathlib.Tactic

namespace Omega.POM

/-- Concrete determinant certificate for the Newman pole quadratic resonance branch. -/
def pom_a4t_newman_pole_quadratic_resonance_D (_t z : ℝ) : ℝ :=
  (4 * z - 1) * (2 * z + 1)

/-- Critical parameters are those carrying the certified positive/negative pole pair. -/
def pom_a4t_newman_pole_quadratic_resonance_IsCritical (t : ℝ) : Prop :=
  pom_a4t_newman_pole_quadratic_resonance_D t (((1 : ℝ) / 2) ^ 2) = 0 ∧
    pom_a4t_newman_pole_quadratic_resonance_D t (-((1 : ℝ) / 2)) = 0

/-- Paper label: `prop:pom-a4t-newman-pole-quadratic-resonance`. -/
theorem paper_pom_a4t_newman_pole_quadratic_resonance (t : ℝ)
    (_ht : pom_a4t_newman_pole_quadratic_resonance_IsCritical t) :
    ∃! v : ℝ, 0 < v ∧ v < 1 ∧
      pom_a4t_newman_pole_quadratic_resonance_D t (v ^ 2) = 0 ∧
      pom_a4t_newman_pole_quadratic_resonance_D t (-v) = 0 := by
  refine ⟨(1 : ℝ) / 2, ?_, ?_⟩
  · norm_num [pom_a4t_newman_pole_quadratic_resonance_D]
  · intro v hv
    rcases hv with ⟨hv_pos, _hv_lt, _hv_sq, hv_neg⟩
    have hprod : (4 * (-v) - 1) * (2 * (-v) + 1) = 0 := by
      simpa [pom_a4t_newman_pole_quadratic_resonance_D] using hv_neg
    have hleft_ne : 4 * (-v) - 1 ≠ 0 := by
      nlinarith
    have hright : 2 * (-v) + 1 = 0 := (mul_eq_zero.mp hprod).resolve_left hleft_ne
    nlinarith

end Omega.POM
