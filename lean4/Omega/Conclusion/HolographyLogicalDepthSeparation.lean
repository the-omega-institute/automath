import Mathlib

namespace Omega.Conclusion

/-- Abstract prefix-machine data for the holography/logical-depth construction. -/
structure conclusion_holography_logical_depth_separation_data where
  conclusion_holography_logical_depth_separation_g : ℕ → ℕ
  conclusion_holography_logical_depth_separation_prefixComplexity : ℕ → ℕ
  conclusion_holography_logical_depth_separation_timeComplexity : ℕ → ℕ → ℕ
  conclusion_holography_logical_depth_separation_depth : ℕ → ℕ → ℕ
  conclusion_holography_logical_depth_separation_C₁ : ℕ
  conclusion_holography_logical_depth_separation_C₂ : ℕ
  conclusion_holography_logical_depth_separation_m₀ : ℕ
  conclusion_holography_logical_depth_separation_ordinary_bound :
    ∀ m,
      conclusion_holography_logical_depth_separation_m₀ ≤ m →
        conclusion_holography_logical_depth_separation_prefixComplexity m ≤
          conclusion_holography_logical_depth_separation_C₁ * Nat.log 2 (m + 1)
  conclusion_holography_logical_depth_separation_depth_spec :
    ∀ m s t,
      conclusion_holography_logical_depth_separation_depth s m ≤ t →
        conclusion_holography_logical_depth_separation_timeComplexity t m ≤
          conclusion_holography_logical_depth_separation_prefixComplexity m + s
  conclusion_holography_logical_depth_separation_missing_block_lower :
    ∀ m,
      conclusion_holography_logical_depth_separation_m₀ ≤ m →
        conclusion_holography_logical_depth_separation_prefixComplexity m +
            conclusion_holography_logical_depth_separation_C₂ * Nat.log 2 (m + 1) <
          conclusion_holography_logical_depth_separation_timeComplexity
            (conclusion_holography_logical_depth_separation_g m) m

namespace conclusion_holography_logical_depth_separation_data

def conclusion_holography_logical_depth_separation_prefixLength (m : ℕ) : ℕ :=
  m * (m + 1) / 2

def conclusion_holography_logical_depth_separation_claim
    (D : conclusion_holography_logical_depth_separation_data) : Prop :=
  ∀ m,
    D.conclusion_holography_logical_depth_separation_m₀ ≤ m →
      D.conclusion_holography_logical_depth_separation_prefixComplexity m ≤
          D.conclusion_holography_logical_depth_separation_C₁ * Nat.log 2 (m + 1) ∧
        D.conclusion_holography_logical_depth_separation_g m <
          D.conclusion_holography_logical_depth_separation_depth
            (D.conclusion_holography_logical_depth_separation_C₂ * Nat.log 2 (m + 1)) m

end conclusion_holography_logical_depth_separation_data

open conclusion_holography_logical_depth_separation_data

/-- Paper label: `thm:conclusion-holography-logical-depth-separation`. -/
theorem paper_conclusion_holography_logical_depth_separation
    (D : conclusion_holography_logical_depth_separation_data) :
    conclusion_holography_logical_depth_separation_claim D := by
  intro m hm
  refine ⟨D.conclusion_holography_logical_depth_separation_ordinary_bound m hm, ?_⟩
  by_contra hnot
  have hdepth_le :
      D.conclusion_holography_logical_depth_separation_depth
          (D.conclusion_holography_logical_depth_separation_C₂ * Nat.log 2 (m + 1)) m ≤
        D.conclusion_holography_logical_depth_separation_g m := by
    exact Nat.le_of_not_gt hnot
  have hfast :=
    D.conclusion_holography_logical_depth_separation_depth_spec m
      (D.conclusion_holography_logical_depth_separation_C₂ * Nat.log 2 (m + 1))
      (D.conclusion_holography_logical_depth_separation_g m) hdepth_le
  have hmissing :=
    D.conclusion_holography_logical_depth_separation_missing_block_lower m hm
  exact (not_lt_of_ge hfast) hmissing

end Omega.Conclusion
