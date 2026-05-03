import Omega.POM.MicrocanonicalFoldEntropy

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `thm:conclusion-oracle-macrospectrum-complete-implementation-opaque`. -/
theorem paper_conclusion_oracle_macrospectrum_complete_implementation_opaque
    {α : Type*} [Fintype α] [DecidableEq α] (d : α → ℕ)
    (hmass : 0 < Omega.POM.microcanonicalTotalMass d) :
    Omega.POM.microcanonicalFoldClassCount d =
        Nat.factorial (Omega.POM.microcanonicalTotalMass d) /
          ∏ x ∈ (Finset.univ : Finset α), Nat.factorial (d x) ∧
      Omega.POM.microcanonicalFoldEntropyMainTerm d =
        (Omega.POM.microcanonicalTotalMass d : ℝ) *
          Omega.POM.microcanonicalFoldShannonEntropy d := by
  exact Omega.POM.paper_pom_microcanonical_fold_entropy d hmass

end Omega.Conclusion
