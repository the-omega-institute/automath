import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-godel-leyang-finite-sample-identifiability`. -/
theorem paper_conclusion_godel_leyang_finite_sample_identifiability
    {Digit Quot : Type*} [DecidableEq Digit] [DecidableEq Quot]
    (D empirical : Finset Digit) (modBT : Digit → Quot) («section» : Quot → Digit)
    (delta coverageProb : ℝ)
    (hCover : empirical.image modBT = D.image modBT)
    (hSectionLeft : ∀ d ∈ D, «section» (modBT d) = d)
    (hSectionMem : ∀ q ∈ D.image modBT, «section» q ∈ D)
    (hCoupon : 1 - delta ≤ coverageProb) :
    empirical.image modBT = D.image modBT ∧
      (empirical.image modBT).image «section» = D ∧
        1 - delta ≤ coverageProb := by
  refine ⟨hCover, ?_, hCoupon⟩
  apply Finset.ext
  intro d
  constructor
  · intro hd
    rcases Finset.mem_image.mp hd with ⟨q, hq, rfl⟩
    exact hSectionMem q (by simpa [hCover] using hq)
  · intro hd
    refine Finset.mem_image.mpr ⟨modBT d, ?_, ?_⟩
    · simpa [hCover] using Finset.mem_image.mpr ⟨d, hd, rfl⟩
    · exact hSectionLeft d hd

end Omega.Conclusion
