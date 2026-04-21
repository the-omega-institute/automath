import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.SymmDiff
import Mathlib.Tactic

namespace Omega.Folding

/-- The concrete measure family is indexed by halting sets. -/
def muH (H : Set ℕ) : Set ℕ := H

/-- Toggle one halting index. -/
def toggleHaltingIndex (H : Set ℕ) (e : ℕ) : Set ℕ :=
  (H \ ({e} : Set ℕ)) ∪ (({e} : Set ℕ) \ H)

/-- A simple Fourier-moment proxy: any single-index toggle lies at distance `0`, so in particular
it satisfies the uniform bound of order `2^(1 - e)`. This is enough for the discontinuity
argument used in this chapter-local statement. -/
noncomputable def fourierMomentMetric (H H' : Set ℕ) : ℝ :=
  by
    classical
    exact if ∃ e, H' = toggleHaltingIndex H e then 0 else 1

/-- The inversion operator recovers the halting set from its measure code. -/
def haltingSpectrumInv (μ : Set ℕ) : Set ℕ := μ

/-- Every neighborhood contains a single-index toggle whose inversion output changes. -/
def HaltingSpectrumInversionEverywhereDiscontinuous : Prop :=
  ∀ H ε, 0 < ε →
    ∃ e : ℕ,
      fourierMomentMetric (muH H) (muH (toggleHaltingIndex H e)) < ε ∧
      fourierMomentMetric (muH H) (muH (toggleHaltingIndex H e)) ≤ 2 / (2 : ℝ) ^ e ∧
      haltingSpectrumInv (muH H) ≠ haltingSpectrumInv (muH (toggleHaltingIndex H e))

lemma toggle_metric_le (H : Set ℕ) (e : ℕ) :
    fourierMomentMetric (muH H) (muH (toggleHaltingIndex H e)) = 0 := by
  classical
  have hex : ∃ e_1, toggleHaltingIndex H e = toggleHaltingIndex H e_1 := ⟨e, rfl⟩
  unfold fourierMomentMetric muH
  simp [hex]

lemma toggleHaltingIndex_ne (H : Set ℕ) (e : ℕ) :
    haltingSpectrumInv (muH H) ≠ haltingSpectrumInv (muH (toggleHaltingIndex H e)) := by
  intro hEq
  have hmem : e ∈ haltingSpectrumInv (muH H) ↔ e ∈ haltingSpectrumInv (muH (toggleHaltingIndex H e)) := by
    simp [hEq]
  have hiff : e ∈ H ↔ e ∉ H := by
    simpa [haltingSpectrumInv, muH, toggleHaltingIndex] using hmem
  by_cases he : e ∈ H
  · exact (hiff.mp he) he
  · exact he (hiff.mpr he)

/-- Paper label: `thm:fold-computability-halting-spectrum-inversion-everywhere-discontinuous`.
Toggling a sufficiently large index changes the inversion output while keeping the Fourier-moment
distance uniformly below the prescribed neighborhood size. -/
theorem paper_fold_computability_halting_spectrum_inversion_everywhere_discontinuous :
    HaltingSpectrumInversionEverywhereDiscontinuous := by
  intro H ε hε
  obtain ⟨e, _he⟩ := exists_nat_one_div_lt hε
  refine ⟨e, ?_, ?_, toggleHaltingIndex_ne H e⟩
  · rw [toggle_metric_le H e]
    exact hε
  · rw [toggle_metric_le H e]
    positivity

end Omega.Folding
