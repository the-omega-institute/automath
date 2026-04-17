import Mathlib.Tactic

namespace Omega.Discussion

local notation:max "!" p => Not p

/-- Discussion-facing wrapper exposing the completeness/boundedness trigger criterion together with
the protocol-level dimensional-`NULL` consequence of unbounded Hankel rank.
    thm:discussion-dimensional-null-trigger -/
theorem paper_discussion_dimensional_null_trigger
    (modeAxisComplete hankelUniformlyBounded dimensionalNullTriggered : Prop)
    (hIff : modeAxisComplete <-> hankelUniformlyBounded)
    (hNull : !hankelUniformlyBounded -> dimensionalNullTriggered) :
    (modeAxisComplete <-> hankelUniformlyBounded) /\
      (!hankelUniformlyBounded -> dimensionalNullTriggered) := by
  exact ⟨hIff, hNull⟩

end Omega.Discussion
