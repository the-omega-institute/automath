import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Paper label: `thm:conclusion-realinput40-gauge-difference-modgaussian-cubic`. Write `u` for
the cubic scaling parameter `m^{1/3}` and truncate the pressure after the cubic term. After the
substitution `θ = z / u`, centering removes the linear part and multiplying by the Gaussian factor
with scale `t_m = κ₂ u` leaves exactly the cubic mod-Gaussian limit function. -/
theorem paper_conclusion_realinput40_gauge_difference_modgaussian_cubic
    (u : ℂ) (hu : u ≠ 0) :
    let κ₁ : ℂ := (4 : ℂ) / 9
    let κ₂ : ℂ := (118 : ℂ) / 243
    let κ₃ : ℂ := (-1174 : ℂ) / 2187
    let paper_label_conclusion_realinput40_gauge_difference_modgaussian_cubic_pressure :
        ℂ → ℂ := fun θ => κ₁ * θ + (κ₂ * θ ^ 2) / 2 + (κ₃ * θ ^ 3) / 6
    let paper_label_conclusion_realinput40_gauge_difference_modgaussian_cubic_tm : ℂ := κ₂ * u
    let paper_label_conclusion_realinput40_gauge_difference_modgaussian_cubic_centered_mgf :
        ℂ → ℂ := fun z =>
          Complex.exp
            (u ^ 3 *
              (paper_label_conclusion_realinput40_gauge_difference_modgaussian_cubic_pressure
                  (z / u) -
                κ₁ * (z / u)))
    ∀ z : ℂ,
      Complex.exp
          (-(paper_label_conclusion_realinput40_gauge_difference_modgaussian_cubic_tm * z ^ 2) /
            2) *
        paper_label_conclusion_realinput40_gauge_difference_modgaussian_cubic_centered_mgf z =
          Complex.exp ((κ₃ * z ^ 3) / 6) := by
  dsimp
  intro z
  have hexponent :
      u ^ 3 * (((118 : ℂ) / 243 * (z / u) ^ 2) / 2 + (((-1174 : ℂ) / 2187) * (z / u) ^ 3) / 6) =
        ((((118 : ℂ) / 243) * u) * z ^ 2) / 2 + (((-1174 : ℂ) / 2187) * z ^ 3) / 6 := by
    field_simp [hu]
  calc
    Complex.exp (-((((118 : ℂ) / 243) * u) * z ^ 2) / 2) *
        Complex.exp
          (u ^ 3 *
            (((4 : ℂ) / 9 * (z / u) + (((118 : ℂ) / 243) * (z / u) ^ 2) / 2 +
                  (((-1174 : ℂ) / 2187) * (z / u) ^ 3) / 6) -
              (4 : ℂ) / 9 * (z / u))) =
        Complex.exp
          (-((((118 : ℂ) / 243) * u) * z ^ 2) / 2 +
            u ^ 3 *
              (((4 : ℂ) / 9 * (z / u) + (((118 : ℂ) / 243) * (z / u) ^ 2) / 2 +
                    (((-1174 : ℂ) / 2187) * (z / u) ^ 3) / 6) -
                (4 : ℂ) / 9 * (z / u))) := by
          rw [← Complex.exp_add]
    _ = Complex.exp
          (-((((118 : ℂ) / 243) * u) * z ^ 2) / 2 +
            u ^ 3 *
              ((((118 : ℂ) / 243) * (z / u) ^ 2) / 2 +
                (((-1174 : ℂ) / 2187) * (z / u) ^ 3) / 6)) := by
          congr 1
          ring
    _ = Complex.exp
          (-((((118 : ℂ) / 243) * u) * z ^ 2) / 2 +
            ((((118 : ℂ) / 243) * u) * z ^ 2) / 2 +
              (((-1174 : ℂ) / 2187) * z ^ 3) / 6) := by
          rw [hexponent]
          simp [add_assoc]
    _ = Complex.exp (((((-1174 : ℂ) / 2187) * z ^ 3) / 6)) := by
          congr 1
          ring_nf

end

end Omega.Conclusion
