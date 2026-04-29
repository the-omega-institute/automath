import Mathlib.Tactic

open Finset

namespace Omega.Preliminaries.EmpiricalFrequencyBounds

/-- Paper seed: empirical frequency lies in the unit interval. -/
theorem paper_empirical_frequency_mem_unit_interval_seeds
    (N : ℕ) (hN : 0 < N) (A : Fin N → Prop) [DecidablePred A] :
    0 ≤ ((Finset.univ.filter A).card : ℝ) / (N : ℝ) ∧
    ((Finset.univ.filter A).card : ℝ) / (N : ℝ) ≤ 1 := by
  have hNR : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast hN
  have hcardle : (Finset.univ.filter A).card ≤ N := by
    simpa using (Finset.card_filter_le (s := (Finset.univ : Finset (Fin N))) (p := A))
  refine ⟨?_, ?_⟩
  · positivity
  · rw [div_le_one₀ hNR]
    exact_mod_cast hcardle

theorem paper_empirical_frequency_mem_unit_interval_package
    (N : ℕ) (hN : 0 < N) (A : Fin N → Prop) [DecidablePred A] :
    0 ≤ ((Finset.univ.filter A).card : ℝ) / (N : ℝ) ∧
    ((Finset.univ.filter A).card : ℝ) / (N : ℝ) ≤ 1 :=
  paper_empirical_frequency_mem_unit_interval_seeds N hN A

theorem paper_empirical_frequency_mem_unit_interval
    (N : ℕ) (hN : 0 < N) (A : Fin N → Prop) [DecidablePred A] :
    0 ≤ ((Finset.univ.filter A).card : ℝ) / (N : ℝ) ∧
    ((Finset.univ.filter A).card : ℝ) / (N : ℝ) ≤ 1 := by
  exact paper_empirical_frequency_mem_unit_interval_package N hN A

end Omega.Preliminaries.EmpiricalFrequencyBounds
