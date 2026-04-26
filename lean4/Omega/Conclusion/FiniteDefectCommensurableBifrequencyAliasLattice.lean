import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- The phase factor sampled at frequency `ξ` and offset `γ`. -/
def conclusion_finite_defect_commensurable_bifrequency_alias_lattice_phase
    (ξ γ : ℝ) : ℂ :=
  Complex.exp ((((γ * ξ : ℝ) : ℂ) * Complex.I))

lemma conclusion_finite_defect_commensurable_bifrequency_alias_lattice_phase_shift
    (m k : ℤ) (ω γ : ℝ) (hω : 0 < ω) :
    let L : ℝ := 2 * Real.pi / ω
    conclusion_finite_defect_commensurable_bifrequency_alias_lattice_phase ((m : ℝ) * ω)
        (γ + (k : ℝ) * L) =
      conclusion_finite_defect_commensurable_bifrequency_alias_lattice_phase ((m : ℝ) * ω) γ := by
  dsimp [conclusion_finite_defect_commensurable_bifrequency_alias_lattice_phase]
  have hω0 : ω ≠ 0 := hω.ne'
  have hkm : (((k * m : ℤ) : ℝ)) = (k : ℝ) * (m : ℝ) := by
    exact_mod_cast rfl
  have hre :
      (γ + (k : ℝ) * (2 * Real.pi / ω)) * ((m : ℝ) * ω) =
        γ * ((m : ℝ) * ω) + (((k * m : ℤ) : ℝ) * (2 * Real.pi)) := by
    field_simp [hω0]
    rw [hkm]
    ring
  have hexp :
      ((((γ + (k : ℝ) * (2 * Real.pi / ω)) * ((m : ℝ) * ω) : ℝ) : ℂ) * Complex.I) =
        ((((γ * ((m : ℝ) * ω) : ℝ) : ℂ) * Complex.I)) +
          (((k * m : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) := by
    simpa [mul_add, add_mul, mul_assoc] using congrArg (fun t : ℝ => (t : ℂ) * Complex.I) hre
  rw [hexp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- If two sampled frequencies lie in the same positive real lattice `ω · ℤ`, then every integer
shift by `L = 2π / ω` preserves both phase factors. -/
def conclusion_finite_defect_commensurable_bifrequency_alias_lattice_statement
    (ξ ξ' : ℝ) : Prop :=
  ∀ m n : ℤ, ∀ ω : ℝ, 0 < ω →
    ξ = (m : ℝ) * ω → ξ' = (n : ℝ) * ω →
      let L : ℝ := 2 * Real.pi / ω
      ∀ γ : ℝ, ∀ k : ℤ,
        conclusion_finite_defect_commensurable_bifrequency_alias_lattice_phase ξ
            (γ + (k : ℝ) * L) =
          conclusion_finite_defect_commensurable_bifrequency_alias_lattice_phase ξ γ ∧
        conclusion_finite_defect_commensurable_bifrequency_alias_lattice_phase ξ'
            (γ + (k : ℝ) * L) =
          conclusion_finite_defect_commensurable_bifrequency_alias_lattice_phase ξ' γ

theorem paper_conclusion_finite_defect_commensurable_bifrequency_alias_lattice
    (ξ ξ' : ℝ) : conclusion_finite_defect_commensurable_bifrequency_alias_lattice_statement ξ ξ' := by
  intro m n ω hω hξ hξ'
  dsimp
  intro γ k
  constructor
  · simpa [hξ] using
      conclusion_finite_defect_commensurable_bifrequency_alias_lattice_phase_shift m k ω γ hω
  · simpa [hξ'] using
      conclusion_finite_defect_commensurable_bifrequency_alias_lattice_phase_shift n k ω γ hω

end

end Omega.Conclusion
