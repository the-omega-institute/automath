import Omega.POM.MicrocanonicalEscortAllRenyiCollapse

namespace Omega.Conclusion

/-- All positive resolutions on the hot layer share the same Renyi limit profile. -/
def conclusion_oracle_hotlayer_all_renyi_collapse_statement
    (limitProfile : ℝ → ℝ) (conditionalUniformEntropy conditionalEscortEntropy : ℝ → ℝ → ℝ)
    (hotPhasePoint : ℝ) : Prop :=
  ∀ b : ℝ, 0 < b →
    conditionalUniformEntropy hotPhasePoint b = conditionalEscortEntropy hotPhasePoint b ∧
      conditionalUniformEntropy hotPhasePoint b = limitProfile hotPhasePoint

/-- Paper label: `thm:conclusion-oracle-hotlayer-all-renyi-collapse`. -/
theorem paper_conclusion_oracle_hotlayer_all_renyi_collapse
    (limitProfile : ℝ → ℝ) (conditionalUniformEntropy conditionalEscortEntropy : ℝ → ℝ → ℝ)
    (hotPhasePoint phaseLeft phaseRight escortOrder : ℝ)
    (hotPhase_mem : phaseLeft < hotPhasePoint ∧ hotPhasePoint < phaseRight)
    (escortOrder_mem : 0 < escortOrder ∧ escortOrder < 1)
    (uniform_collapse :
      ∀ b : ℝ, 0 < b → conditionalUniformEntropy hotPhasePoint b = limitProfile hotPhasePoint)
    (escort_collapse :
      ∀ b : ℝ, 0 < b → conditionalEscortEntropy hotPhasePoint b = limitProfile hotPhasePoint) :
    conclusion_oracle_hotlayer_all_renyi_collapse_statement limitProfile conditionalUniformEntropy
      conditionalEscortEntropy hotPhasePoint := by
  exact
    Omega.POM.paper_pom_microcanonical_escort_all_renyi_collapse
      limitProfile conditionalUniformEntropy conditionalEscortEntropy hotPhasePoint
      phaseLeft phaseRight escortOrder hotPhase_mem escortOrder_mem
      uniform_collapse escort_collapse

end Omega.Conclusion
