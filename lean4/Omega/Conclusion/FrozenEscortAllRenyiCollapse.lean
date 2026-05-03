import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-frozen-escort-all-renyi-collapse`. -/
theorem paper_conclusion_frozen_escort_all_renyi_collapse
    (renyiRateLimit : Option Real -> Real -> Prop) (gStar : Real)
    (hOne : renyiRateLimit (some 1) gStar)
    (hFinite : forall s : Real, 1 < s -> renyiRateLimit (some s) gStar)
    (hInf : renyiRateLimit none gStar) :
    (forall s : Real, 1 <= s -> renyiRateLimit (some s) gStar) /\
      renyiRateLimit none gStar := by
  refine ⟨?_, hInf⟩
  intro s hs
  rcases lt_or_eq_of_le hs with hslt | hseq
  · exact hFinite s hslt
  · simpa [hseq] using hOne

end Omega.Conclusion
