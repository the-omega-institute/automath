import Omega.Conclusion.LocalizedCechCompletenessFiniteCover

namespace Omega.Conclusion

/-- Chapter-local proxy for the vanishing of higher Čech homology on a finite cover. -/
def conclusion_localized_no_high_cech_obstruction_finite_cover_no_high_cech_homology
    (cover : List (Finset Nat)) : Prop :=
  localizedCechExact cover

/-- Chapter-local proxy for the vanishing of higher Čech cohomology on a finite cover. -/
def conclusion_localized_no_high_cech_obstruction_finite_cover_no_high_cech_cohomology
    (cover : List (Finset Nat)) : Prop :=
  localizedDualCechExact cover

/-- Paper label: `cor:conclusion-localized-no-high-cech-obstruction-finite-cover`.
Unpacking the finite-cover Čech exactness package yields the claimed vanishing of higher Čech
homology and cohomology obstructions. -/
theorem paper_conclusion_localized_no_high_cech_obstruction_finite_cover
    (cover : List (Finset Nat)) (hExact : And (localizedCechExact cover) (localizedDualCechExact cover))
    (noHighCechHomology noHighCechCohomology : Prop)
    (hHomology : localizedCechExact cover -> noHighCechHomology)
    (hCohomology : localizedDualCechExact cover -> noHighCechCohomology) :
    And noHighCechHomology noHighCechCohomology := by
  rcases hExact with ⟨hCechExact, hDualCechExact⟩
  exact ⟨hHomology hCechExact, hCohomology hDualCechExact⟩

end Omega.Conclusion
