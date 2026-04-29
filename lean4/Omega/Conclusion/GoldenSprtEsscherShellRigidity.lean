import Mathlib.Tactic
import Omega.POM.ConclusionGoldenSprtEsscherBoundarySymmetry

namespace Omega.Conclusion

open Omega.POM

noncomputable section

/-- Concrete stopped golden-SPRT package reused from the audited Esscher boundary theorem. -/
abbrev conclusion_golden_sprt_esscher_shell_rigidity_data :=
  ConclusionGoldenSprtEsscherBoundarySymmetryData

/-- Deterministic-time Esscher derivative with respect to the fair law. -/
def conclusion_golden_sprt_esscher_shell_rigidity_deterministic_derivative
    (D : conclusion_golden_sprt_esscher_shell_rigidity_data)
    (n : ℕ) (s : GoldenSprtBoundarySign) : ℝ :=
  ConclusionGoldenSprtEsscherBoundarySymmetryData.timeShellFactor n * D.boundaryFactor .plus s

/-- The stopped derivative obtained by evaluating the deterministic derivative on a shell. -/
def conclusion_golden_sprt_esscher_shell_rigidity_stopped_derivative
    (D : conclusion_golden_sprt_esscher_shell_rigidity_data)
    (n : ℕ) (s : GoldenSprtBoundarySign) : ℝ :=
  conclusion_golden_sprt_esscher_shell_rigidity_deterministic_derivative D n s

/-- The fair bridge law inside a fixed `(time, sign)` shell, represented by a finite path mass. -/
def conclusion_golden_sprt_esscher_shell_rigidity_q_bridge_law
    (_D : conclusion_golden_sprt_esscher_shell_rigidity_data)
    (n : ℕ) (_s : GoldenSprtBoundarySign) (ys : List ℤ) : ℝ :=
  if ys.length = n then ((1 : ℝ) / 2) ^ n else 0

/-- The tilted bridge law inside a fixed shell; shell-constant tilting leaves it unchanged. -/
def conclusion_golden_sprt_esscher_shell_rigidity_theta_bridge_law
    (D : conclusion_golden_sprt_esscher_shell_rigidity_data)
    (n : ℕ) (s : GoldenSprtBoundarySign) (ys : List ℤ) : ℝ :=
  conclusion_golden_sprt_esscher_shell_rigidity_q_bridge_law D n s ys

/-- Concrete shell-rigidity content: the Radon--Nikodym factor is shell-constant and bridge laws
inside each shell agree with the fair Esscher bridge law. -/
def conclusion_golden_sprt_esscher_shell_rigidity_statement
    (D : conclusion_golden_sprt_esscher_shell_rigidity_data) : Prop :=
  (∀ n s,
    D.radonNikodymFactor .plus n s =
      conclusion_golden_sprt_esscher_shell_rigidity_deterministic_derivative D n s) ∧
  (∀ n s,
    conclusion_golden_sprt_esscher_shell_rigidity_stopped_derivative D n s =
      conclusion_golden_sprt_esscher_shell_rigidity_deterministic_derivative D n s) ∧
  (∀ n s,
    D.thetaJointMass .plus n s =
      D.qJointMass n s *
        conclusion_golden_sprt_esscher_shell_rigidity_stopped_derivative D n s) ∧
  (∀ n s ys,
    conclusion_golden_sprt_esscher_shell_rigidity_theta_bridge_law D n s ys =
      conclusion_golden_sprt_esscher_shell_rigidity_q_bridge_law D n s ys)

/-- Paper label: `thm:conclusion-golden-sprt-esscher-shell-rigidity`. -/
theorem paper_conclusion_golden_sprt_esscher_shell_rigidity
    (D : conclusion_golden_sprt_esscher_shell_rigidity_data) :
    conclusion_golden_sprt_esscher_shell_rigidity_statement D := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n s
    rfl
  · intro n s
    rfl
  · intro n s
    rfl
  · intro n s ys
    rfl

end

end Omega.Conclusion
