import Omega.Conclusion.BinfoldFrozenEscortExactRecoveryPhaseTransition
import Omega.Conclusion.EscortTwoStateClosure
import Omega.Conclusion.FrozenBranchTwoScalarClosure

namespace Omega.Conclusion

noncomputable section

/-- The Bernoulli two-state escort collapse, uniformly packaged over the two temperatures and
the tested observable. -/
def conclusion_escort_temperature_bernoulli_then_frozen_degeneracy_bernoulliStatement :
    Prop :=
  ∀ (p q : ℕ) (F : ℝ → ℝ),
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
          conclusion_escort_two_state_closure_theta q * F (1 / Real.goldenRatio)

/-- The frozen endpoint package: affine recovery of the frozen degeneracy scalars plus the
binary max-fiber recovery threshold. -/
def conclusion_escort_temperature_bernoulli_then_frozen_degeneracy_frozenStatement :
    Prop :=
  conclusion_frozen_branch_two_scalar_closure_statement ∧
    ∀ α β : ℕ,
      ((β < α) →
        Filter.Tendsto (fun m => binfoldFrozenEscortReducedSuccess α β m) Filter.atTop
          (nhds 0)) ∧
      ((α < β) →
        Filter.Tendsto (fun m => binfoldFrozenEscortReducedSuccess α β m) Filter.atTop
          (nhds 1))

/-- Paper-facing terminal conjunction for the two-stage collapse. -/
def conclusion_escort_temperature_bernoulli_then_frozen_degeneracy_statement : Prop :=
  conclusion_escort_temperature_bernoulli_then_frozen_degeneracy_bernoulliStatement ∧
    conclusion_escort_temperature_bernoulli_then_frozen_degeneracy_frozenStatement

/-- Paper label: `thm:conclusion-escort-temperature-bernoulli-then-frozen-degeneracy`. -/
theorem paper_conclusion_escort_temperature_bernoulli_then_frozen_degeneracy :
    conclusion_escort_temperature_bernoulli_then_frozen_degeneracy_statement := by
  refine ⟨?_, ?_⟩
  · intro p q F
    exact paper_conclusion_escort_two_state_closure p q F
  · refine ⟨paper_conclusion_frozen_branch_two_scalar_closure, ?_⟩
    intro α β
    exact paper_conclusion_binfold_frozen_escort_exact_recovery_phase_transition α β

end

end Omega.Conclusion
