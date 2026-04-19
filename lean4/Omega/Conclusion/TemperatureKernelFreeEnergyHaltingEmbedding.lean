import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Conclusion.SemanticEquivalenceUndecidable

namespace Omega.Conclusion

/-- The non-halting branch value in the temperature-kernel free-energy law. -/
noncomputable def nonhaltingTemperatureFreeEnergyValue (α : ℝ) : ℝ :=
  (1 - α) * Real.log 2

/-- Temperature schedule driven by the bounded-step halting predicate. -/
noncomputable def haltingTemperatureSchedule
    (α : ℝ) (haltsWithin : ℕ → Prop) [DecidablePred haltsWithin] (q : ℕ) : ℝ :=
  if haltsWithin q then 0 else Real.exp (-(α * (q : ℝ)) * Real.log 2)

/-- Pointwise decidability of the bounded-step halting predicate is the chapter-local notion of a
computable temperature schedule. -/
abbrev HaltingScheduleComputable (haltsWithin : ℕ → Prop) : Prop :=
  PredicatePointwiseDecidable haltsWithin

/-- A bounded-step halting predicate yields a pointwise decidable temperature schedule; halting
forces the eventual zero branch with free energy `log φ`, non-halting forces the Perron-Landauer
branch value `(1 - α) log 2`, and any decider for that free-energy branch would decide the
non-halting predicate.
    thm:conclusion-temperature-kernel-free-energy-halting-embedding -/
theorem paper_conclusion_temperature_kernel_free_energy_halting_embedding
    {Code : Type*} (α : ℝ) (haltsWithin : Code → ℕ → Prop) (nonHalting : Code → Prop)
    (freeEnergy : Code → ℝ)
    (hStepDec : ∀ c, HaltingScheduleComputable (haltsWithin c))
    (hNonhalting_iff : ∀ c, nonHalting c ↔ ∀ q, ¬ haltsWithin c q)
    (hHaltingValue : ∀ c, (∃ q, haltsWithin c q) → freeEnergy c = Real.log Real.goldenRatio)
    (hNonhaltingValue :
      ∀ c, nonHalting c → freeEnergy c = nonhaltingTemperatureFreeEnergyValue α)
    (hGap :
      Real.log Real.goldenRatio ≠ nonhaltingTemperatureFreeEnergyValue α) :
    (∀ c, HaltingScheduleComputable (haltsWithin c)) ∧
      (∀ c, (∃ q, haltsWithin c q) → freeEnergy c = Real.log Real.goldenRatio) ∧
      (∀ c, nonHalting c ↔ freeEnergy c = nonhaltingTemperatureFreeEnergyValue α) ∧
      (Nonempty (∀ c, Decidable (freeEnergy c = nonhaltingTemperatureFreeEnergyValue α)) →
        Nonempty (∀ c, Decidable (nonHalting c))) := by
  have hReduction : ∀ c, nonHalting c ↔ freeEnergy c = nonhaltingTemperatureFreeEnergyValue α := by
    intro c
    constructor
    · exact hNonhaltingValue c
    · intro hEq
      by_contra hNotNonhalting
      have hHalt : ∃ q, haltsWithin c q := by
        by_contra hNoHalt
        apply hNotNonhalting
        exact (hNonhalting_iff c).2 fun q hq => hNoHalt ⟨q, hq⟩
      have hHaltValueEq : freeEnergy c = Real.log Real.goldenRatio := hHaltingValue c hHalt
      exact hGap (hHaltValueEq.symm.trans hEq)
  refine ⟨hStepDec, hHaltingValue, hReduction, ?_⟩
  · intro hDec
    refine ⟨?_⟩
    intro c
    let hDecEq : ∀ c, Decidable (freeEnergy c = nonhaltingTemperatureFreeEnergyValue α) :=
      Classical.choice hDec
    letI := hDecEq c
    exact decidable_of_iff (freeEnergy c = nonhaltingTemperatureFreeEnergyValue α)
      (hReduction c).symm

end Omega.Conclusion
