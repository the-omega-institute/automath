import Mathlib.Tactic
import Omega.Conclusion.HolographyLogicalDepthSeparation

namespace Omega.Conclusion

/-- The arbitrarily slow readout corollary uses the concrete logical-depth data package. -/
abbrev conclusion_holography_arbitrarily_slow_readout_data :=
  conclusion_holography_logical_depth_separation_data

namespace conclusion_holography_arbitrarily_slow_readout_data

def has_constant_program (D : conclusion_holography_arbitrarily_slow_readout_data) : Prop :=
  ∃ L : ℕ, D.conclusion_holography_logical_depth_separation_C₁ ≤ L

def has_infinitely_many_slow_prefixes
    (D : conclusion_holography_arbitrarily_slow_readout_data) : Prop :=
  ∀ M : ℕ,
    ∃ m : ℕ,
      M ≤ m ∧
        D.conclusion_holography_logical_depth_separation_m₀ ≤ m ∧
          D.conclusion_holography_logical_depth_separation_g m <
            D.conclusion_holography_logical_depth_separation_depth
              (D.conclusion_holography_logical_depth_separation_C₂ * Nat.log 2 (m + 1)) m

end conclusion_holography_arbitrarily_slow_readout_data

/-- Paper label: `cor:conclusion-holography-arbitrarily-slow-readout`. -/
theorem paper_conclusion_holography_arbitrarily_slow_readout
    (D : conclusion_holography_arbitrarily_slow_readout_data) :
    D.has_constant_program ∧ D.has_infinitely_many_slow_prefixes := by
  refine ⟨?_, ?_⟩
  · exact ⟨D.conclusion_holography_logical_depth_separation_C₁, le_rfl⟩
  · intro M
    let m := max M D.conclusion_holography_logical_depth_separation_m₀
    have hm₀ : D.conclusion_holography_logical_depth_separation_m₀ ≤ m := by
      exact Nat.le_max_right M D.conclusion_holography_logical_depth_separation_m₀
    have hclaim := paper_conclusion_holography_logical_depth_separation D m hm₀
    refine ⟨m, ?_, hm₀, hclaim.2⟩
    exact Nat.le_max_left M D.conclusion_holography_logical_depth_separation_m₀

end Omega.Conclusion
