import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic
import Omega.POM.MicrocanonicalStreamingProgramRarity

namespace Omega.POM

/-- The logarithmic width budget coming from the branching-program counting term
`n^S * S^(2 S N)`. -/
noncomputable def pom_microcanonical_streaming_program_typical_width_lb_log_budget
    (N S n : ℕ) : ℝ :=
  2 * (S : ℝ) * (N : ℝ) * Real.log S + (S : ℝ) * Real.log n

/-- Paper label: `cor:pom-microcanonical-streaming-program-typical-width-lb`. Once the
branching-program logarithmic count is dominated by the entropy lower bound with an additional
linear gap `c₂ N`, the rarity estimate from
`paper_pom_microcanonical_streaming_program_rarity` upgrades to an explicit exponential bound. -/
def paper_pom_microcanonical_streaming_program_typical_width_lb_statement : Prop :=
  ∀ (D : PomMicrocanonicalStreamingProgramRarityData) (c2 : ℝ),
    0 ≤ c2 →
    Real.log D.programBoundReal ≤
      pom_microcanonical_streaming_program_typical_width_lb_log_budget
        D.layers D.width D.outputAlphabet →
    pom_microcanonical_streaming_program_typical_width_lb_log_budget
        D.layers D.width D.outputAlphabet ≤
      D.entropyLowerBound - c2 * D.layers →
    D.rarityRatio ≤ Real.exp (-c2 * D.layers)

theorem paper_pom_microcanonical_streaming_program_typical_width_lb :
    paper_pom_microcanonical_streaming_program_typical_width_lb_statement := by
  intro D c2 hc2_nonneg hlog_budget hentropy_gap
  rcases paper_pom_microcanonical_streaming_program_rarity D with
    ⟨_, _, hratio_bound, hexponential_form⟩
  have hgap :
      Real.log D.programBoundReal - D.entropyLowerBound ≤ -c2 * D.layers := by
    linarith
  calc
    D.rarityRatio ≤ Real.exp (Real.log D.programBoundReal - D.entropyLowerBound) := by
      simpa [hexponential_form] using hratio_bound
    _ ≤ Real.exp (-c2 * D.layers) := by
      gcongr

end Omega.POM
