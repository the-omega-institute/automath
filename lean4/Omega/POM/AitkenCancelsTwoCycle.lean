import Mathlib.Tactic
import Omega.POM.AitkenDelta2SquareConvergence

namespace Omega.POM

/-- Paper label: `cor:pom-aitken-cancels-two-cycle`. -/
theorem paper_pom_aitken_cancels_two_cycle (R : ℕ → ℂ) (lam1 a ρ : ℂ) (τ : ℝ)
    (hτ : 0 ≤ τ ∧ τ < ‖ρ‖ ∧ ‖ρ‖ < 1)
    (hR : ∃ C q0, ∀ q ≥ q0, ‖R q - (lam1 + a * ρ ^ q)‖ ≤ C * τ ^ q) :
    ∃ C' q1, ∀ q ≥ q1, ‖Omega.POM.aitkenDelta2 R q - lam1‖ ≤ C' * τ ^ q := by
  rcases hR with ⟨C, q0, hRtail⟩
  have hρ0 : 0 < ‖ρ‖ := lt_of_le_of_lt hτ.1 hτ.2.1
  have hAsymptotic : HasTwoStepAsymptotic R lam1 a 0 ρ := by
    refine ⟨τ, ?_⟩
    refine And.intro hτ.1 ?_
    refine And.intro hτ.2.1 ?_
    refine Exists.intro C ?_
    refine Exists.intro q0 ?_
    intro q hq
    simpa using hRtail q hq
  let w : TwoStepAsymptoticWitness R := {
    sInf := lam1
    A := a
    B := 0
    ρ := ρ
    hρ0 := hρ0
    hρ1 := hτ.2.2
    hAsymptotic := hAsymptotic
  }
  have hw : Nonempty (TwoStepAsymptoticWitness R) := ⟨w⟩
  let w' : TwoStepAsymptoticWitness R := Classical.choice hw
  have hw'sInf : w'.sInf = lam1 := by
    exact two_step_asymptotic_limit_unique w'.hρ1 w'.hAsymptotic hτ.2.2 hAsymptotic
  refine ⟨0, 0, ?_⟩
  intro q hq
  simp [Omega.POM.aitkenDelta2, w', aitkenLimit_eq_choice hw, hw'sInf]

end Omega.POM
