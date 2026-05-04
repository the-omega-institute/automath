import Omega.Conclusion.FiniteDefectProfileMinimalCauchyRank

namespace Omega.Conclusion

/-- Concrete wrapper for the finite-defect profile whose intrinsic rank is read from the profile. -/
structure conclusion_finite_defect_profile_intrinsic_minimal_rank_data where
  conclusion_finite_defect_profile_intrinsic_minimal_rank_profile :
    conclusion_finite_defect_profile_minimal_cauchy_rank_data

namespace conclusion_finite_defect_profile_intrinsic_minimal_rank_data

/-- The rank exposed by the canonical finite-defect Cauchy kernel. -/
def conclusion_finite_defect_profile_intrinsic_minimal_rank_rank
    (D : conclusion_finite_defect_profile_intrinsic_minimal_rank_data) : ℕ :=
  conclusion_finite_defect_profile_minimal_cauchy_rank_kernel_rank
    D.conclusion_finite_defect_profile_intrinsic_minimal_rank_profile

/-- The atom count of the finite-defect profile. -/
def conclusion_finite_defect_profile_intrinsic_minimal_rank_atom_count
    (D : conclusion_finite_defect_profile_intrinsic_minimal_rank_data) : ℕ :=
  D.conclusion_finite_defect_profile_intrinsic_minimal_rank_profile.κ

/--
The intrinsic-minimal-rank corollary: the exposed rank is the profile atom count, that atom count
is attainable, and every exact Cauchy representation has rank at least that count.
-/
def conclusion_finite_defect_profile_intrinsic_minimal_rank_holds
    (D : conclusion_finite_defect_profile_intrinsic_minimal_rank_data) : Prop :=
  D.conclusion_finite_defect_profile_intrinsic_minimal_rank_rank =
      D.conclusion_finite_defect_profile_intrinsic_minimal_rank_atom_count ∧
    conclusion_finite_defect_profile_minimal_cauchy_rank_exact_cauchy_representation
      D.conclusion_finite_defect_profile_intrinsic_minimal_rank_profile
      D.conclusion_finite_defect_profile_intrinsic_minimal_rank_atom_count ∧
    ∀ r : ℕ,
      conclusion_finite_defect_profile_minimal_cauchy_rank_exact_cauchy_representation
        D.conclusion_finite_defect_profile_intrinsic_minimal_rank_profile r →
        D.conclusion_finite_defect_profile_intrinsic_minimal_rank_atom_count ≤ r

end conclusion_finite_defect_profile_intrinsic_minimal_rank_data

open conclusion_finite_defect_profile_intrinsic_minimal_rank_data

/-- Paper label: `cor:conclusion-finite-defect-profile-intrinsic-minimal-rank`. -/
theorem paper_conclusion_finite_defect_profile_intrinsic_minimal_rank
    (D : conclusion_finite_defect_profile_intrinsic_minimal_rank_data) :
    D.conclusion_finite_defect_profile_intrinsic_minimal_rank_holds := by
  rcases
    paper_conclusion_finite_defect_profile_minimal_cauchy_rank
      D.conclusion_finite_defect_profile_intrinsic_minimal_rank_profile with
    ⟨hattainKernel, hlower, hrank⟩
  refine ⟨?_, ?_, ?_⟩
  · exact hrank
  · simpa [conclusion_finite_defect_profile_intrinsic_minimal_rank_atom_count] using
      hattainKernel
  · intro r hr
    simpa [conclusion_finite_defect_profile_intrinsic_minimal_rank_atom_count] using
      hlower r hr

end Omega.Conclusion
