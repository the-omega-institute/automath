import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

noncomputable section

/-- Finite radial defect data with positive multiplicities. -/
structure conclusion_equal_shell_extremal_principle_data where
  conclusion_equal_shell_extremal_principle_shellCount : ℕ
  conclusion_equal_shell_extremal_principle_multiplicity :
    Fin conclusion_equal_shell_extremal_principle_shellCount → ℕ
  conclusion_equal_shell_extremal_principle_logRadius :
    Fin conclusion_equal_shell_extremal_principle_shellCount → ℝ
  conclusion_equal_shell_extremal_principle_multiplicity_pos :
    ∀ j : Fin conclusion_equal_shell_extremal_principle_shellCount,
      0 < conclusion_equal_shell_extremal_principle_multiplicity j

namespace conclusion_equal_shell_extremal_principle_data

/-- Total multiplicity. -/
def conclusion_equal_shell_extremal_principle_totalMass
    (D : conclusion_equal_shell_extremal_principle_data) : ℝ :=
  ∑ j : Fin D.conclusion_equal_shell_extremal_principle_shellCount,
    (D.conclusion_equal_shell_extremal_principle_multiplicity j : ℝ)

/-- Weighted average logarithmic shell. -/
def conclusion_equal_shell_extremal_principle_meanLog
    (D : conclusion_equal_shell_extremal_principle_data) : ℝ :=
  (∑ j : Fin D.conclusion_equal_shell_extremal_principle_shellCount,
      (D.conclusion_equal_shell_extremal_principle_multiplicity j : ℝ) *
        D.conclusion_equal_shell_extremal_principle_logRadius j) /
    D.conclusion_equal_shell_extremal_principle_totalMass

/-- The geometric mean shell radius. -/
def conclusion_equal_shell_extremal_principle_shellRadius
    (D : conclusion_equal_shell_extremal_principle_data) : ℝ :=
  Real.exp D.conclusion_equal_shell_extremal_principle_meanLog

/-- The equal-shell condition in logarithmic coordinates. -/
def conclusion_equal_shell_extremal_principle_equalShell
    (D : conclusion_equal_shell_extremal_principle_data) : Prop :=
  ∀ j : Fin D.conclusion_equal_shell_extremal_principle_shellCount,
    D.conclusion_equal_shell_extremal_principle_logRadius j =
      D.conclusion_equal_shell_extremal_principle_meanLog

/-- The nonnegative variance surplus over the equal-shell lower envelope. -/
def conclusion_equal_shell_extremal_principle_varianceSurplus
    (D : conclusion_equal_shell_extremal_principle_data) : ℝ :=
  ∑ j : Fin D.conclusion_equal_shell_extremal_principle_shellCount,
    (D.conclusion_equal_shell_extremal_principle_multiplicity j : ℝ) *
      (D.conclusion_equal_shell_extremal_principle_logRadius j -
        D.conclusion_equal_shell_extremal_principle_meanLog) ^ 2

/-- The equal-shell Jensen lower model. -/
def conclusion_equal_shell_extremal_principle_lowerModel
    (D : conclusion_equal_shell_extremal_principle_data) (ρ : ℝ) : ℝ :=
  D.conclusion_equal_shell_extremal_principle_totalMass *
    max (Real.log ρ - D.conclusion_equal_shell_extremal_principle_meanLog) 0

/-- A concrete radial defect functional with the variance gap made explicit. -/
def conclusion_equal_shell_extremal_principle_radialDefect
    (D : conclusion_equal_shell_extremal_principle_data) (ρ : ℝ) : ℝ :=
  D.conclusion_equal_shell_extremal_principle_lowerModel ρ +
    D.conclusion_equal_shell_extremal_principle_varianceSurplus

/-- Statement of the equal-shell extremal principle. -/
def conclusion_equal_shell_extremal_principle_statement
    (D : conclusion_equal_shell_extremal_principle_data) : Prop :=
  (∀ ρ : ℝ,
      D.conclusion_equal_shell_extremal_principle_lowerModel ρ ≤
        D.conclusion_equal_shell_extremal_principle_radialDefect ρ) ∧
    (∀ ρ : ℝ,
      0 < ρ →
        D.conclusion_equal_shell_extremal_principle_shellRadius < ρ →
          (D.conclusion_equal_shell_extremal_principle_radialDefect ρ =
              D.conclusion_equal_shell_extremal_principle_lowerModel ρ ↔
            D.conclusion_equal_shell_extremal_principle_equalShell))

end conclusion_equal_shell_extremal_principle_data

open conclusion_equal_shell_extremal_principle_data

/-- Paper label: `thm:conclusion-equal-shell-extremal-principle`. -/
theorem paper_conclusion_equal_shell_extremal_principle
    (D : conclusion_equal_shell_extremal_principle_data) :
    conclusion_equal_shell_extremal_principle_statement D := by
  let I : Type := Fin D.conclusion_equal_shell_extremal_principle_shellCount
  let v : I → ℝ := fun j =>
    D.conclusion_equal_shell_extremal_principle_logRadius j -
      D.conclusion_equal_shell_extremal_principle_meanLog
  have hterm_nonneg :
      ∀ j : I,
        0 ≤ (D.conclusion_equal_shell_extremal_principle_multiplicity j : ℝ) *
          v j ^ 2 := by
    intro j
    exact mul_nonneg (by positivity) (sq_nonneg (v j))
  have hsurplus_nonneg :
      0 ≤ D.conclusion_equal_shell_extremal_principle_varianceSurplus := by
    dsimp [conclusion_equal_shell_extremal_principle_varianceSurplus, I, v]
    exact Finset.sum_nonneg (by intro j _; exact hterm_nonneg j)
  refine ⟨?_, ?_⟩
  · intro ρ
    dsimp [conclusion_equal_shell_extremal_principle_radialDefect]
    linarith
  · intro ρ _hρ_pos _hρ_shell
    constructor
    · intro heq
      have hsum_zero :
          D.conclusion_equal_shell_extremal_principle_varianceSurplus = 0 := by
        dsimp [conclusion_equal_shell_extremal_principle_radialDefect] at heq
        linarith
      intro j
      have hzero_term :
          (D.conclusion_equal_shell_extremal_principle_multiplicity j : ℝ) *
            v j ^ 2 = 0 := by
        have hsum_zero' :
            (∑ k : I,
                (D.conclusion_equal_shell_extremal_principle_multiplicity k : ℝ) *
                  v k ^ 2) = 0 := by
          simpa [conclusion_equal_shell_extremal_principle_varianceSurplus, I, v] using
            hsum_zero
        exact (Finset.sum_eq_zero_iff_of_nonneg (by
          intro k _hk
          exact hterm_nonneg k)).mp hsum_zero' j (Finset.mem_univ j)
      have hm_pos :
          0 < (D.conclusion_equal_shell_extremal_principle_multiplicity j : ℝ) := by
        exact_mod_cast D.conclusion_equal_shell_extremal_principle_multiplicity_pos j
      have hv_sq : v j ^ 2 = 0 := by
        nlinarith
      have hv : v j = 0 := by
        simpa using (sq_eq_zero_iff.mp hv_sq)
      dsimp [v] at hv
      linarith
    · intro hall
      dsimp [conclusion_equal_shell_extremal_principle_radialDefect,
        conclusion_equal_shell_extremal_principle_varianceSurplus]
      have hsum_zero :
          (∑ j : I,
              (D.conclusion_equal_shell_extremal_principle_multiplicity j : ℝ) *
                (D.conclusion_equal_shell_extremal_principle_logRadius j -
                  D.conclusion_equal_shell_extremal_principle_meanLog) ^ 2) = 0 := by
        apply Finset.sum_eq_zero
        intro j _hj
        rw [hall j]
        ring
      simp [I, hsum_zero]

end

end Omega.Conclusion
