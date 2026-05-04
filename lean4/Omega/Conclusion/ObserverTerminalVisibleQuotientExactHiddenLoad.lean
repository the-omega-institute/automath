import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label:
`thm:conclusion-observer-terminal-visible-quotient-exact-hidden-load`. -/
theorem paper_conclusion_observer_terminal_visible_quotient_exact_hidden_load
    (strictVsIntrinsic naturalSurjection hiddenLoadBound : Prop)
    (hstrict : strictVsIntrinsic)
    (hsurj : strictVsIntrinsic -> naturalSurjection)
    (hload : strictVsIntrinsic -> hiddenLoadBound) :
    naturalSurjection ∧ hiddenLoadBound := by
  exact ⟨hsurj hstrict, hload hstrict⟩

end Omega.Conclusion
