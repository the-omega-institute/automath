import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-fibadic-cyclotomic-bundles-recover-conductor-depth-map`. -/
theorem paper_conclusion_fibadic_cyclotomic_bundles_recover_conductor_depth_map {N D : Type*}
    [DecidableEq D] (appearsIn : D → N → Prop) (depth : N → D)
    (hunique : ∀ n d, appearsIn d n ↔ depth n = d) :
    ∀ n d, depth n = d ↔ appearsIn d n ∧ ∀ e, appearsIn e n → e = d := by
  intro n d
  constructor
  · intro hdepth
    constructor
    · exact (hunique n d).2 hdepth
    · intro e he
      have heq : depth n = e := (hunique n e).1 he
      exact heq.symm.trans hdepth
  · intro h
    exact (hunique n d).1 h.1

end Omega.Conclusion
