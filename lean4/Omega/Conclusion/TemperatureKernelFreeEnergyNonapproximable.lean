import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Conclusion.TemperatureKernelFreeEnergyHaltingEmbedding

namespace Omega.Conclusion

/-- A rational interval algorithm is `δ`-short if every output interval contains the target free
energy and has width strictly below `δ`. -/
def conclusion_temperature_kernel_free_energy_nonapproximable_short_interval
    {Code : Type*} (freeEnergy : Code → ℝ) (delta : ℝ) (interval : Code → ℚ × ℚ) : Prop :=
  ∀ c,
    ((interval c).1 : ℝ) ≤ freeEnergy c ∧
      freeEnergy c ≤ (interval c).2 ∧
      ((((interval c).2 - (interval c).1 : ℚ) : ℝ) < delta)

private lemma conclusion_temperature_kernel_free_energy_nonapproximable_abs_sub_le_of_mem_interval
    {a b u v : ℝ} (hu₁ : a ≤ u) (hu₂ : u ≤ b) (hv₁ : a ≤ v) (hv₂ : v ≤ b) :
    |u - v| ≤ b - a := by
  refine abs_le.mpr ?_
  constructor <;> linarith

/-- Concrete formulation of
`cor:conclusion-temperature-kernel-free-energy-nonapproximable`: once the halting embedding
produces the two separated branch values `log φ` and `(1 - α) log 2`, any uniformly short rational
interval oracle would decide which branch holds, contradicting undecidability of the non-halting
predicate. -/
def conclusion_temperature_kernel_free_energy_nonapproximable_statement : Prop :=
  ∀ {Code : Type*} (α delta : ℝ) (haltsWithin : Code → ℕ → Prop) (nonHalting : Code → Prop)
      (freeEnergy : Code → ℝ),
    (∀ c, HaltingScheduleComputable (haltsWithin c)) →
    (∀ c, nonHalting c ↔ ∀ q, ¬ haltsWithin c q) →
    (∀ c, (∃ q, haltsWithin c q) → freeEnergy c = Real.log Real.goldenRatio) →
    (∀ c, nonHalting c → freeEnergy c = nonhaltingTemperatureFreeEnergyValue α) →
    0 < delta →
    2 * delta <
      |Real.log Real.goldenRatio - nonhaltingTemperatureFreeEnergyValue α| →
    ¬ Nonempty (∀ c, Decidable (nonHalting c)) →
    ¬ ∃ interval : Code → ℚ × ℚ,
      conclusion_temperature_kernel_free_energy_nonapproximable_short_interval freeEnergy delta
        interval

/-- Paper label: `cor:conclusion-temperature-kernel-free-energy-nonapproximable`. -/
theorem paper_conclusion_temperature_kernel_free_energy_nonapproximable :
    conclusion_temperature_kernel_free_energy_nonapproximable_statement := by
  intro Code α delta haltsWithin nonHalting freeEnergy hStepDec hNonhalting_iff hHaltingValue
    hNonhaltingValue hDeltaPos hGap hUndecidable hInterval
  rcases hInterval with ⟨interval, hInterval⟩
  have hNe :
      Real.log Real.goldenRatio ≠ nonhaltingTemperatureFreeEnergyValue α := by
    intro hEq
    rw [← hEq, sub_self, abs_zero] at hGap
    linarith
  rcases
      paper_conclusion_temperature_kernel_free_energy_halting_embedding α haltsWithin nonHalting
        freeEnergy hStepDec hNonhalting_iff hHaltingValue hNonhaltingValue hNe with
    ⟨_, _, hReduction, hDecReduction⟩
  have hDecEq :
      Nonempty
        (∀ c,
          Decidable
            (freeEnergy c = nonhaltingTemperatureFreeEnergyValue α)) := by
    refine ⟨?_⟩
    intro c
    by_cases hMem :
        ((interval c).1 : ℝ) ≤ nonhaltingTemperatureFreeEnergyValue α ∧
          nonhaltingTemperatureFreeEnergyValue α ≤ (interval c).2
    · apply isTrue
      by_contra hNotEq
      have hNotNonhalting : ¬ nonHalting c := by
        intro hNon
        exact hNotEq ((hReduction c).mp hNon)
      have hHalts : ∃ q, haltsWithin c q := by
        by_contra hNoHalts
        apply hNotNonhalting
        exact (hNonhalting_iff c).2 fun q hq => hNoHalts ⟨q, hq⟩
      have hValue : freeEnergy c = Real.log Real.goldenRatio := hHaltingValue c hHalts
      rcases hInterval c with ⟨hLeft, hRight, hShort⟩
      have hLogMem :
          ((interval c).1 : ℝ) ≤ Real.log Real.goldenRatio ∧
            Real.log Real.goldenRatio ≤ (interval c).2 := by
        simpa [hValue] using And.intro hLeft hRight
      have hAbs :
          |Real.log Real.goldenRatio - nonhaltingTemperatureFreeEnergyValue α| ≤
            ((interval c).2 : ℝ) - (interval c).1 := by
        exact
          conclusion_temperature_kernel_free_energy_nonapproximable_abs_sub_le_of_mem_interval
            hLogMem.1 hLogMem.2 hMem.1 hMem.2
      have hGap' :
          delta <
            |Real.log Real.goldenRatio - nonhaltingTemperatureFreeEnergyValue α| := by
        linarith
      have hWidthGt : delta < ((interval c).2 : ℝ) - (interval c).1 :=
        lt_of_lt_of_le hGap' hAbs
      have hShort' : ((interval c).2 : ℝ) - (interval c).1 < delta := by
        norm_num at hShort ⊢
        exact hShort
      have : delta < delta := lt_of_lt_of_le hWidthGt hShort'.le
      exact lt_irrefl _ this
    · apply isFalse
      intro hEq
      rcases hInterval c with ⟨hLeft, hRight, _⟩
      apply hMem
      simpa [hEq] using And.intro hLeft hRight
  exact hUndecidable (hDecReduction hDecEq)

end Omega.Conclusion
