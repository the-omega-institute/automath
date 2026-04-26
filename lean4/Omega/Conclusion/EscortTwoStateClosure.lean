import Omega.Conclusion.BinfoldEscortLimitManifoldOneDimensionalKlCompletion

namespace Omega.Conclusion

noncomputable section

/-- The Bernoulli terminal-bit parameter of the golden bin-fold escort family. -/
def conclusion_escort_two_state_closure_theta (q : ℕ) : ℝ :=
  binfoldEscortTheta Real.goldenRatio q

/-- The limiting terminal-bit law, with `true` denoting the lower atom `φ⁻¹`. -/
def conclusion_escort_two_state_closure_terminalLaw (q : ℕ) : Bool → ℝ
  | true => conclusion_escort_two_state_closure_theta q
  | false => 1 - conclusion_escort_two_state_closure_theta q

/-- The limiting scaled fiber-weight observable, split by the terminal bit. -/
def conclusion_escort_two_state_closure_scaledFiberLimit (q : ℕ) (F : ℝ → ℝ) : ℝ :=
  conclusion_escort_two_state_closure_terminalLaw q false * F 1 +
    conclusion_escort_two_state_closure_terminalLaw q true * F (1 / Real.goldenRatio)

/-- The limiting KL geometry of the two-state escort closure. -/
def conclusion_escort_two_state_closure_kl (p q : ℕ) : ℝ :=
  bernoulliPairwiseKL (conclusion_escort_two_state_closure_theta p)
    (conclusion_escort_two_state_closure_theta q)

/-- Paper label: `thm:conclusion-escort-two-state-closure`. The escort limit geometry factors
through the Bernoulli terminal-bit parameter `θ(q)`, and every scaled fiber-weight observable
splits into the two terminal-bit atoms with masses `θ(q)` and `1 - θ(q)`. -/
theorem paper_conclusion_escort_two_state_closure (p q : ℕ) (F : ℝ → ℝ) :
    conclusion_escort_two_state_closure_theta q =
        1 / (1 + Real.goldenRatio ^ (q + 1)) ∧
      conclusion_escort_two_state_closure_kl p q =
        conclusion_escort_two_state_closure_theta q *
            Real.log
              (conclusion_escort_two_state_closure_theta q /
                conclusion_escort_two_state_closure_theta p) +
          (1 - conclusion_escort_two_state_closure_theta q) *
            Real.log
              ((1 - conclusion_escort_two_state_closure_theta q) /
                (1 - conclusion_escort_two_state_closure_theta p)) ∧
      conclusion_escort_two_state_closure_terminalLaw q true =
        conclusion_escort_two_state_closure_theta q ∧
      conclusion_escort_two_state_closure_terminalLaw q false =
        1 - conclusion_escort_two_state_closure_theta q ∧
      conclusion_escort_two_state_closure_scaledFiberLimit q F =
        (1 - conclusion_escort_two_state_closure_theta q) * F 1 +
          conclusion_escort_two_state_closure_theta q * F (1 / Real.goldenRatio) := by
  refine ⟨rfl, ?_, rfl, rfl, rfl⟩
  rfl

end

end Omega.Conclusion
