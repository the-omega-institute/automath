import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-global-null-pure-cohomological-remainder`. Once the local
`NULL` alternatives are exhausted and the only remaining global failure is the `H²`
obstruction, unreadability is equivalent to that obstruction. -/
theorem paper_conclusion_global_null_pure_cohomological_remainder
    (globalReadable h2Obstruction localNullExhausted : Prop) (hExhausted : localNullExhausted)
    (hOnlyObstruction : localNullExhausted → (globalReadable ↔ ¬ h2Obstruction)) :
    (¬ globalReadable ↔ h2Obstruction) := by
  classical
  have hread : globalReadable ↔ ¬ h2Obstruction := hOnlyObstruction hExhausted
  constructor
  · intro hnotReadable
    by_contra hnotObstruction
    exact hnotReadable (hread.mpr hnotObstruction)
  · intro hObstruction hReadable
    exact (hread.mp hReadable) hObstruction

end Omega.Conclusion
