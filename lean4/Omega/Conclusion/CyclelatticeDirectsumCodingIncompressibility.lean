import Mathlib

namespace Omega.Conclusion

noncomputable section

def conclusion_cyclelattice_directsum_coding_incompressibility_volumeLeadingTerm
    (m r : ℕ) (R τ : ℝ) : ℝ :=
  (m : ℝ) * (r : ℝ) * Real.log R - ((m : ℝ) / 2) * Real.log τ

def conclusion_cyclelattice_directsum_coding_incompressibility_binaryLeadingTerm
    (m r : ℕ) (R τ : ℝ) : ℝ :=
  conclusion_cyclelattice_directsum_coding_incompressibility_volumeLeadingTerm m r R τ /
    Real.log 2

def conclusion_cyclelattice_directsum_coding_incompressibility_oneSectorBinaryTerm
    (r : ℕ) (R τ : ℝ) : ℝ :=
  ((r : ℝ) * Real.log R - (1 / 2 : ℝ) * Real.log τ) / Real.log 2

def conclusion_cyclelattice_directsum_coding_incompressibility_statement : Prop :=
  ∀ (m r : ℕ) (R τ : ℝ),
    conclusion_cyclelattice_directsum_coding_incompressibility_binaryLeadingTerm m r R τ =
      (m : ℝ) *
        conclusion_cyclelattice_directsum_coding_incompressibility_oneSectorBinaryTerm r R τ

/-- Paper label: `cor:conclusion-cyclelattice-directsum-coding-incompressibility`. -/
theorem paper_conclusion_cyclelattice_directsum_coding_incompressibility :
    conclusion_cyclelattice_directsum_coding_incompressibility_statement := by
  intro m r R τ
  unfold conclusion_cyclelattice_directsum_coding_incompressibility_binaryLeadingTerm
  unfold conclusion_cyclelattice_directsum_coding_incompressibility_volumeLeadingTerm
  unfold conclusion_cyclelattice_directsum_coding_incompressibility_oneSectorBinaryTerm
  ring

end

end Omega.Conclusion
