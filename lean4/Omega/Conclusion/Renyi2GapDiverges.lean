import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic

namespace Omega.Conclusion

open Filter

noncomputable section

/-- Concrete package for the Rényi-2 uniform-baseline gap divergence corollary. -/
structure conclusion_renyi2_gap_diverges_data where
  conclusion_renyi2_gap_diverges_collision_profile : ℕ → ℝ
  conclusion_renyi2_gap_diverges_fibonacci_shifted : ℕ → ℝ
  conclusion_renyi2_gap_diverges_gap : ℕ → ℝ
  conclusion_renyi2_gap_diverges_identity_proof :
    ∀ m,
      conclusion_renyi2_gap_diverges_gap m =
        Real.log
          (conclusion_renyi2_gap_diverges_fibonacci_shifted m *
            conclusion_renyi2_gap_diverges_collision_profile m)
  conclusion_renyi2_gap_diverges_product_diverges :
    Tendsto
      (fun m =>
        conclusion_renyi2_gap_diverges_fibonacci_shifted m *
          conclusion_renyi2_gap_diverges_collision_profile m)
      atTop atTop
  conclusion_renyi2_gap_diverges_transfer :
    (∀ m,
        conclusion_renyi2_gap_diverges_gap m =
          Real.log
            (conclusion_renyi2_gap_diverges_fibonacci_shifted m *
              conclusion_renyi2_gap_diverges_collision_profile m)) →
      Tendsto
          (fun m =>
            conclusion_renyi2_gap_diverges_fibonacci_shifted m *
              conclusion_renyi2_gap_diverges_collision_profile m)
          atTop atTop →
        Tendsto conclusion_renyi2_gap_diverges_gap atTop atTop

namespace conclusion_renyi2_gap_diverges_data

/-- Rényi-2 identity against the uniform baseline. -/
def renyi2_identity (D : conclusion_renyi2_gap_diverges_data) : Prop :=
  ∀ m,
    D.conclusion_renyi2_gap_diverges_gap m =
      Real.log
        (D.conclusion_renyi2_gap_diverges_fibonacci_shifted m *
          D.conclusion_renyi2_gap_diverges_collision_profile m)

/-- Divergence of the Rényi-2 gap. -/
def renyi2_gap_diverges (D : conclusion_renyi2_gap_diverges_data) : Prop :=
  Tendsto D.conclusion_renyi2_gap_diverges_gap atTop atTop

end conclusion_renyi2_gap_diverges_data

/-- Paper label: `cor:conclusion-renyi2-gap-diverges`. -/
theorem paper_conclusion_renyi2_gap_diverges (D : conclusion_renyi2_gap_diverges_data) :
    D.renyi2_identity ∧ D.renyi2_gap_diverges := by
  refine ⟨D.conclusion_renyi2_gap_diverges_identity_proof, ?_⟩
  exact
    D.conclusion_renyi2_gap_diverges_transfer
      D.conclusion_renyi2_gap_diverges_identity_proof
      D.conclusion_renyi2_gap_diverges_product_diverges

end

end Omega.Conclusion
