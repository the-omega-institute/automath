import Mathlib.Tactic

namespace Omega.Conclusion

/-- Deep ambiguity at every finite prefix prevents an injective paired readout when the auxiliary
register depends on only one finite prefix. -/
theorem paper_conclusion_pcdim_lowerbound_deep_ambiguity {Ω X K : Type*} (f : Ω → X)
    (r : Ω → K) (samePrefix : ℕ → Ω → Ω → Prop)
    (hdepends : ∃ N0, ∀ {ω ω' : Ω}, samePrefix N0 ω ω' → r ω = r ω')
    (hdeep : ∀ N, ∃ ω ω' : Ω, ω ≠ ω' ∧ f ω = f ω' ∧ samePrefix N ω ω') :
    ¬ Function.Injective (fun ω : Ω => (f ω, r ω)) := by
  rintro hinj
  rcases hdepends with ⟨N0, hN0⟩
  rcases hdeep N0 with ⟨ω, ω', hne, hf, hpref⟩
  have hr : r ω = r ω' := hN0 hpref
  have hpair : (f ω, r ω) = (f ω', r ω') := by
    exact Prod.ext hf hr
  exact hne (hinj hpair)

end Omega.Conclusion
