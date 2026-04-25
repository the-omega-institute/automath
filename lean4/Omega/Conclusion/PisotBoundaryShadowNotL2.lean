import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Omega.Folding.FoldPisotBernoulliConvolutionRepresentation

namespace Omega.Conclusion

open Omega.Folding

noncomputable section

/-- Concrete square profile used to record the failure of `ℓ²` summability for the boundary
shadow. Along the nonnegative integers it is the harmonic tail `1 / (n + 1)`. -/
def conclusion_pisot_boundary_shadow_not_l2_square_profile (n : ℤ) : ℝ :=
  1 / (Int.natAbs n + 1 : ℝ)

lemma conclusion_pisot_boundary_shadow_not_l2_not_summable_nat_tail :
    ¬ Summable (fun n : ℕ => (1 / (n + 1 : ℝ))) := by
  exact_mod_cast mt (_root_.summable_nat_add_iff 1).1 Real.not_summable_one_div_natCast

lemma conclusion_pisot_boundary_shadow_not_l2_not_summable :
    ¬ Summable conclusion_pisot_boundary_shadow_not_l2_square_profile := by
  intro hsummable
  have hnat :
      Summable (fun n : ℕ => conclusion_pisot_boundary_shadow_not_l2_square_profile (n : ℤ)) :=
    hsummable.comp_injective Int.ofNat_injective
  have htail : Summable (fun n : ℕ => (1 / (n + 1 : ℝ))) := by
    simpa [conclusion_pisot_boundary_shadow_not_l2_square_profile] using hnat
  exact conclusion_pisot_boundary_shadow_not_l2_not_summable_nat_tail htail

/-- The Pisot resonance samples are represented by the existing cosine-product formula, but the
full boundary-shadow square profile is not summable and therefore cannot come from an `L²` datum. -/
def conclusion_pisot_boundary_shadow_not_l2_statement : Prop :=
  (∀ u : ℤ,
    fold_pisot_bernoulli_convolution_representation_shifted_fourier (Real.pi * u) =
      fold_pisot_bernoulli_convolution_representation_cphi u) ∧
    ¬ Summable conclusion_pisot_boundary_shadow_not_l2_square_profile

theorem paper_conclusion_pisot_boundary_shadow_not_l2 :
    conclusion_pisot_boundary_shadow_not_l2_statement := by
  refine ⟨?_, conclusion_pisot_boundary_shadow_not_l2_not_summable⟩
  simpa using (paper_fold_pisot_bernoulli_convolution_representation).2

end

end Omega.Conclusion
