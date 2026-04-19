import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Paper-facing wrapper: each of the three orthogonal failure axes independently obstructs a
legal readout when the other two conditions are met.
    prop:cdim-null-witness-nonsubstitutable -/
theorem paper_cdim_null_witness_nonsubstitutable (legalReadout outBudget cechBudget hardBudget : Prop)
    (hOut : cechBudget → hardBudget → ¬ outBudget → ¬ legalReadout)
    (hCech : outBudget → hardBudget → ¬ cechBudget → ¬ legalReadout)
    (hHard : outBudget → cechBudget → ¬ hardBudget → ¬ legalReadout) :
    ((cechBudget ∧ hardBudget ∧ ¬ outBudget) → ¬ legalReadout) ∧
      ((outBudget ∧ hardBudget ∧ ¬ cechBudget) → ¬ legalReadout) ∧
      ((outBudget ∧ cechBudget ∧ ¬ hardBudget) → ¬ legalReadout) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hcb, hhb, hob⟩
    exact hOut hcb hhb hob
  · rintro ⟨hob, hhb, hcb⟩
    exact hCech hob hhb hcb
  · rintro ⟨hob, hcb, hhb⟩
    exact hHard hob hcb hhb

end Omega.CircleDimension
