import Mathlib.Tactic

/-- Paper label: `thm:xi-time-part9q-critical-flatness-holonomy-identity`. Equal dimensions
through the holonomy rank identify trivial holonomy, critical uniqueness, and strict convexity. -/
theorem paper_xi_time_part9q_critical_flatness_holonomy_identity
    (extEqDim flatDim holRank : ℕ) (holTrivial criticalUnique strictConvex : Prop)
    (hExt : extEqDim = holRank) (hFlat : flatDim = holRank)
    (hHol : holTrivial ↔ holRank = 0) (hCrit : criticalUnique ↔ extEqDim = 0)
    (hStrict : strictConvex ↔ flatDim = 0) :
    extEqDim = holRank ∧ flatDim = holRank ∧ (holTrivial ↔ criticalUnique) ∧
      (criticalUnique ↔ strictConvex) := by
  refine ⟨hExt, hFlat, ?_, ?_⟩
  · constructor
    · intro h
      exact hCrit.mpr (hExt.trans (hHol.mp h))
    · intro h
      exact hHol.mpr (hExt.symm.trans (hCrit.mp h))
  · constructor
    · intro h
      exact hStrict.mpr (hFlat.trans (hExt.symm.trans (hCrit.mp h)))
    · intro h
      exact hCrit.mpr (hExt.trans (hFlat.symm.trans (hStrict.mp h)))
