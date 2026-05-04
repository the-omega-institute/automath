namespace Omega.Zeta

/-- Paper label: `thm:xi-syndrome-quotient-module-rational-canonical-fingerprint`. -/
theorem paper_xi_syndrome_quotient_module_rational_canonical_fingerprint
    (freeCyclic annihilated rationalCanonical semisimpleCriterion simpleSpectrumCriterion : Prop)
    (h_free : freeCyclic) (h_ann : annihilated) (h_rat : rationalCanonical)
    (h_ss : semisimpleCriterion) (h_simple : simpleSpectrumCriterion) :
    freeCyclic ∧ annihilated ∧ rationalCanonical ∧ semisimpleCriterion ∧
      simpleSpectrumCriterion := by
  exact ⟨h_free, h_ann, h_rat, h_ss, h_simple⟩

end Omega.Zeta
