import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import Omega.Conclusion.TemperatureKernelFreeEnergyHaltingEmbedding

namespace Omega.Conclusion

noncomputable section

/-- Base-`d` logarithm used in the spectral-gap threshold. -/
def conclusion_temperature_kernel_free_energy_halting_embedding_subfull_spectrum_logBase
    (d x : ℝ) : ℝ :=
  Real.log x / Real.log d

/-- The halting branch value for the base-`d` temperature kernel. -/
def conclusion_temperature_kernel_free_energy_halting_embedding_subfull_spectrum_haltingValue
    (α d : ℝ) : ℝ :=
  (1 - α) * Real.log d

/-- The non-halting branch value supplied by the subfull Perron radius `λ`. -/
def conclusion_temperature_kernel_free_energy_halting_embedding_subfull_spectrum_nonhaltingValue
    (lam : ℝ) : ℝ :=
  Real.log lam

/-- Concrete subfull-spectrum admissibility for a symmetric nonnegative matrix witness. -/
def conclusion_temperature_kernel_free_energy_halting_embedding_subfull_spectrum_admissible
    {n : Type*} [Fintype n] [DecidableEq n] (spectralRadius : Matrix n n ℝ → ℝ)
    (A : Matrix n n ℝ) (lam d : ℝ) : Prop :=
  A.transpose = A ∧ (∀ i j, 0 ≤ A i j) ∧ spectralRadius A = lam ∧ lam < d

/-- Paper-facing abstract subfull-spectrum halting embedding statement. -/
def conclusion_temperature_kernel_free_energy_halting_embedding_subfull_spectrum_statement : Prop :=
  ∀ {Code n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (spectralRadius : Matrix n n ℝ → ℝ) (α lam d : ℝ) (haltsWithin : Code → ℕ → Prop)
    (nonHalting : Code → Prop) (freeEnergy : Code → ℝ),
    1 < d →
    0 < lam →
    conclusion_temperature_kernel_free_energy_halting_embedding_subfull_spectrum_admissible
      spectralRadius A lam d →
    (∀ c, HaltingScheduleComputable (haltsWithin c)) →
    (∀ c, nonHalting c ↔ ∀ q, ¬ haltsWithin c q) →
    (∀ c, (∃ q, haltsWithin c q) →
      freeEnergy c =
        conclusion_temperature_kernel_free_energy_halting_embedding_subfull_spectrum_haltingValue
          α d) →
    (∀ c, nonHalting c →
      freeEnergy c =
        conclusion_temperature_kernel_free_energy_halting_embedding_subfull_spectrum_nonhaltingValue
          lam) →
    α <
      1 -
        conclusion_temperature_kernel_free_energy_halting_embedding_subfull_spectrum_logBase d lam →
    (∀ c, HaltingScheduleComputable (haltsWithin c)) ∧
      (∀ c, (∃ q, haltsWithin c q) →
        freeEnergy c =
          conclusion_temperature_kernel_free_energy_halting_embedding_subfull_spectrum_haltingValue
            α d) ∧
      (∀ c, nonHalting c ↔
        freeEnergy c =
          conclusion_temperature_kernel_free_energy_halting_embedding_subfull_spectrum_nonhaltingValue
            lam) ∧
      (Nonempty
          (∀ c,
            Decidable
              (freeEnergy c =
                conclusion_temperature_kernel_free_energy_halting_embedding_subfull_spectrum_nonhaltingValue
                  lam)) →
        Nonempty (∀ c, Decidable (nonHalting c)))

/-- Paper label:
`thm:conclusion-temperature-kernel-free-energy-halting-embedding-subfull-spectrum`. -/
theorem
    paper_conclusion_temperature_kernel_free_energy_halting_embedding_subfull_spectrum :
    conclusion_temperature_kernel_free_energy_halting_embedding_subfull_spectrum_statement := by
  intro Code n _ _ A spectralRadius α lam d haltsWithin nonHalting freeEnergy hd hlam hA hStepDec
    hNonhalting_iff hHaltingValue hNonhaltingValue hα
  have _hSubfull : lam < d := hA.2.2.2
  have hdlog_pos : 0 < Real.log d := Real.log_pos hd
  have hmul_lt :
      α * Real.log d <
        (1 -
            conclusion_temperature_kernel_free_energy_halting_embedding_subfull_spectrum_logBase d
              lam) *
          Real.log d := by
    exact mul_lt_mul_of_pos_right hα hdlog_pos
  have hgap_lt :
      conclusion_temperature_kernel_free_energy_halting_embedding_subfull_spectrum_nonhaltingValue
          lam <
        conclusion_temperature_kernel_free_energy_halting_embedding_subfull_spectrum_haltingValue
          α d := by
    have hrewrite :
        (1 -
              conclusion_temperature_kernel_free_energy_halting_embedding_subfull_spectrum_logBase
                d lam) *
            Real.log d =
          Real.log d - Real.log lam := by
      unfold
        conclusion_temperature_kernel_free_energy_halting_embedding_subfull_spectrum_logBase
      field_simp [hdlog_pos.ne']
    rw [hrewrite] at hmul_lt
    unfold
      conclusion_temperature_kernel_free_energy_halting_embedding_subfull_spectrum_nonhaltingValue
    unfold
      conclusion_temperature_kernel_free_energy_halting_embedding_subfull_spectrum_haltingValue
    nlinarith
  have hGap :
      conclusion_temperature_kernel_free_energy_halting_embedding_subfull_spectrum_haltingValue α d ≠
        conclusion_temperature_kernel_free_energy_halting_embedding_subfull_spectrum_nonhaltingValue
          lam := by
    intro hEq
    rw [hEq] at hgap_lt
    exact lt_irrefl _ hgap_lt
  have hReduction :
      ∀ c,
        nonHalting c ↔
          freeEnergy c =
            conclusion_temperature_kernel_free_energy_halting_embedding_subfull_spectrum_nonhaltingValue
              lam := by
    intro c
    constructor
    · exact hNonhaltingValue c
    · intro hEq
      by_contra hNotNonhalting
      have hHalt : ∃ q, haltsWithin c q := by
        by_contra hNoHalt
        apply hNotNonhalting
        exact (hNonhalting_iff c).2 fun q hq => hNoHalt ⟨q, hq⟩
      have hHaltValueEq :
          freeEnergy c =
            conclusion_temperature_kernel_free_energy_halting_embedding_subfull_spectrum_haltingValue
              α d :=
        hHaltingValue c hHalt
      exact hGap (hHaltValueEq.symm.trans hEq)
  refine ⟨hStepDec, hHaltingValue, hReduction, ?_⟩
  intro hDec
  refine ⟨?_⟩
  intro c
  let hDecEq :
      ∀ c,
        Decidable
          (freeEnergy c =
            conclusion_temperature_kernel_free_energy_halting_embedding_subfull_spectrum_nonhaltingValue
              lam) :=
    Classical.choice hDec
  letI := hDecEq c
  exact
    decidable_of_iff
      (freeEnergy c =
        conclusion_temperature_kernel_free_energy_halting_embedding_subfull_spectrum_nonhaltingValue
          lam)
      (hReduction c).symm

end

end Omega.Conclusion
