import Omega.Conclusion.FoldbinMultiplicityMellinTwoSidedUnification
import Omega.Conclusion.FoldbinMultiplicityMellinFiniteSupportRigidity
import Omega.Conclusion.TqftHighGenusBottomSpectrumPeeling

namespace Omega.Conclusion

/-- Collision-side sampling of the master Mellin kernel recovers the positive moments. -/
def conclusion_mellin_master_kernel_two_sided_completeness_collisionMomentSide : Prop :=
  ∀ D : ConclusionFoldbinMultiplicityMellinTwoSidedUnificationData,
    ∀ q : ℕ,
      conclusion_foldbin_multiplicity_mellin_two_sided_unification_kernel D (Sum.inl q) =
        conclusion_foldbin_multiplicity_mellin_two_sided_unification_collision_moment D q

/-- Genus-side sampling of the same master Mellin kernel recovers the genus amplitudes. -/
def conclusion_mellin_master_kernel_two_sided_completeness_genusAmplitudeSide : Prop :=
  ∀ D : ConclusionFoldbinMultiplicityMellinTwoSidedUnificationData,
    ∀ g : ℕ,
      conclusion_foldbin_multiplicity_mellin_two_sided_unification_kernel D (Sum.inr g) =
        conclusion_foldbin_multiplicity_mellin_two_sided_unification_genus_amplitude D g

/-- Positive integer Mellin samples determine the finite histogram. -/
def conclusion_mellin_master_kernel_two_sided_completeness_leftSamplingDeterminesHistogram :
    Prop :=
  ∀ D : conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_data,
    (∀ q : Fin D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_supportSize,
      D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_positiveMoment
          D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_leftMultiplicity q =
        D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_positiveMoment
          D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_rightMultiplicity q) ∧
      D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_leftMultiplicity =
        D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_rightMultiplicity

/-- Genus-side Mellin samples determine the finite histogram. -/
def conclusion_mellin_master_kernel_two_sided_completeness_rightSamplingDeterminesHistogram :
    Prop :=
  ∀ D : conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_data,
    (∀ q : Fin D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_supportSize,
      D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_genusSample
          D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_leftMultiplicity q =
        D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_genusSample
          D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_rightMultiplicity q) ∧
      D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_leftMultiplicity =
        D.conclusion_foldbin_multiplicity_mellin_finite_support_rigidity_rightMultiplicity

/-- High-genus sampling peels the finite spectrum from the minimal sector upward. -/
def conclusion_mellin_master_kernel_two_sided_completeness_highGenusTomography : Prop :=
  ∀ {s : ℕ} (δ μ : Fin s → ℕ), (∀ j, 0 < δ j) → StrictMono δ →
    ∀ r : Fin s,
      Filter.Tendsto
        (fun g : ℕ =>
          (μ r : ℝ) +
            ∑ j : {j : Fin s // r < j},
              (μ (j : Fin s) : ℝ) *
                (((δ r : ℝ) / (δ (j : Fin s) : ℝ)) ^ (2 * g - 2)))
        Filter.atTop (nhds (μ r : ℝ))

/-- Concrete conjunction for the paper-facing master-kernel completeness wrapper. -/
def conclusion_mellin_master_kernel_two_sided_completeness_statement : Prop :=
  conclusion_mellin_master_kernel_two_sided_completeness_collisionMomentSide ∧
    conclusion_mellin_master_kernel_two_sided_completeness_genusAmplitudeSide ∧
    conclusion_mellin_master_kernel_two_sided_completeness_leftSamplingDeterminesHistogram ∧
    conclusion_mellin_master_kernel_two_sided_completeness_rightSamplingDeterminesHistogram ∧
    conclusion_mellin_master_kernel_two_sided_completeness_highGenusTomography

/-- Paper label: `thm:conclusion-mellin-master-kernel-two-sided-completeness`. -/
theorem paper_conclusion_mellin_master_kernel_two_sided_completeness :
    conclusion_mellin_master_kernel_two_sided_completeness_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro D q
    exact (paper_conclusion_foldbin_multiplicity_mellin_two_sided_unification D).1 q
  · intro D g
    exact (paper_conclusion_foldbin_multiplicity_mellin_two_sided_unification D).2.1 g
  · intro D
    exact ⟨(paper_conclusion_foldbin_multiplicity_mellin_finite_support_rigidity D).1,
      (paper_conclusion_foldbin_multiplicity_mellin_finite_support_rigidity D).2.2⟩
  · intro D
    exact ⟨(paper_conclusion_foldbin_multiplicity_mellin_finite_support_rigidity D).2.1,
      (paper_conclusion_foldbin_multiplicity_mellin_finite_support_rigidity D).2.2⟩
  · intro s δ μ hδ_pos hδ_strict r
    exact paper_conclusion_tqft_high_genus_bottom_spectrum_peeling δ μ hδ_pos hδ_strict r

end Omega.Conclusion
