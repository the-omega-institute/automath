import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

open Filter
open scoped Topology

noncomputable section

namespace Omega.Conclusion

/-- The fixed full-shift entropy scale used for ambiguity-shell codimension. -/
def conclusion_ambiguity_shell_sync_exponent_fractal_codimension_identity_logTwo : ℝ :=
  Real.log 2

/-- Entropy gap between the full two-shift and the ambiguity-shell spectral radius. -/
def conclusion_ambiguity_shell_sync_exponent_fractal_codimension_identity_entropyGap
    (rho : ℝ) : ℝ :=
  conclusion_ambiguity_shell_sync_exponent_fractal_codimension_identity_logTwo - Real.log rho

/-- Hausdorff codimension in the natural prefix ultrametric. -/
def conclusion_ambiguity_shell_sync_exponent_fractal_codimension_identity_codim
    (htop : ℝ) : ℝ :=
  (conclusion_ambiguity_shell_sync_exponent_fractal_codimension_identity_logTwo - htop) /
    conclusion_ambiguity_shell_sync_exponent_fractal_codimension_identity_logTwo

/-- Perron--Frobenius exponential tail model for the unsynchronized ambiguity shell. -/
def conclusion_ambiguity_shell_sync_exponent_fractal_codimension_identity_tailModel
    (c eps : ℝ) (n : ℕ) : ℝ :=
  c * Real.exp (-eps * (n : ℝ))

/-- Concrete asymptotic input for the Perron--Frobenius tail formula. -/
def conclusion_ambiguity_shell_sync_exponent_fractal_codimension_identity_pfTail
    (tail : ℕ → ℝ) (c eps : ℝ) : Prop :=
  Tendsto
    (fun n : ℕ =>
      tail n /
        conclusion_ambiguity_shell_sync_exponent_fractal_codimension_identity_tailModel c eps n)
    atTop (𝓝 1)

/-- Concrete algebraic statement: the PF tail exponent, the entropy gap, and the Hausdorff
codimension formula identify the same number. -/
def conclusion_ambiguity_shell_sync_exponent_fractal_codimension_identity_statement : Prop :=
  ∀ (rho htop codim eps c : ℝ) (tail : ℕ → ℝ),
    conclusion_ambiguity_shell_sync_exponent_fractal_codimension_identity_logTwo ≠ 0 →
      conclusion_ambiguity_shell_sync_exponent_fractal_codimension_identity_pfTail tail c eps →
        eps =
          conclusion_ambiguity_shell_sync_exponent_fractal_codimension_identity_entropyGap rho →
          htop = Real.log rho →
            codim =
              conclusion_ambiguity_shell_sync_exponent_fractal_codimension_identity_codim htop →
              conclusion_ambiguity_shell_sync_exponent_fractal_codimension_identity_pfTail
                  tail c eps ∧
                eps =
                  conclusion_ambiguity_shell_sync_exponent_fractal_codimension_identity_logTwo -
                    htop ∧
                  eps =
                    conclusion_ambiguity_shell_sync_exponent_fractal_codimension_identity_logTwo *
                      codim

/-- Paper label:
`thm:conclusion-ambiguity-shell-sync-exponent-fractal-codimension-identity`. -/
theorem paper_conclusion_ambiguity_shell_sync_exponent_fractal_codimension_identity :
    conclusion_ambiguity_shell_sync_exponent_fractal_codimension_identity_statement := by
  intro rho htop codim eps c tail hlogTwo htail heps hhtop hcodim
  refine ⟨htail, ?_, ?_⟩
  · rw [heps, hhtop]
    rfl
  · rw [heps, hcodim, hhtop]
    simp [conclusion_ambiguity_shell_sync_exponent_fractal_codimension_identity_entropyGap,
      conclusion_ambiguity_shell_sync_exponent_fractal_codimension_identity_codim]
    field_simp [hlogTwo]

end Omega.Conclusion
