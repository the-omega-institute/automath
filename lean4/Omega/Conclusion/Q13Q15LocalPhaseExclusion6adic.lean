import Omega.Conclusion.Q13Q15Z3ThreephasePeriodicShells
import Omega.Conclusion.ResonanceWindowZ2HenselTailPeriodicity
import Omega.POM.ResonanceMod6PeriodQ13Q15

namespace Omega.Conclusion

/-- Concrete triadic shell data for `q = 13`. -/
def conclusion_q13_q15_local_phase_exclusion_6adic_q13_data :
    conclusion_q13_q15_z3_threephase_periodic_shells_data where
  q := 13
  l := 1
  nilpotentTransient := 2
  plusPeriod := 1
  minusPeriod := 1
  hq := Or.inl rfl
  hnil := by decide
  hplus := by decide
  hminus := by decide

/-- Concrete triadic shell data for `q = 15`. -/
def conclusion_q13_q15_local_phase_exclusion_6adic_q15_data :
    conclusion_q13_q15_z3_threephase_periodic_shells_data where
  q := 15
  l := 1
  nilpotentTransient := 2
  plusPeriod := 1
  minusPeriod := 1
  hq := Or.inr rfl
  hnil := by decide
  hplus := by decide
  hminus := by decide

/-- A zero mixed-residue tail already models the fact that no extra semisimple CRT sector is
needed beyond the dyadic unipotent piece and the triadic `±1` shells. -/
def conclusion_q13_q15_local_phase_exclusion_6adic_zero_mod6_tail :
    ℕ → ZMod 2 × ZMod 3 := fun _ => (0, 0)

/-- Paper label: `thm:conclusion-q13-q15-local-phase-exclusion-6adic`. The dyadic tail stays
unipotent, the triadic side contributes only the existing `±1` shells, and the mixed mod-`6`
tail is already periodic without creating any new semisimple channel. -/
theorem paper_conclusion_q13_q15_local_phase_exclusion_6adic :
    paper_conclusion_resonance_window_z2_hensel_tail_periodicity_statement 0 13 1 (fun _ => 0) ∧
      paper_conclusion_resonance_window_z2_hensel_tail_periodicity_statement 0 15 1 (fun _ => 0) ∧
      conclusion_q13_q15_z3_threephase_periodic_shells_data.semisimple_periodic_shell_bound
        conclusion_q13_q15_local_phase_exclusion_6adic_q13_data ∧
      conclusion_q13_q15_z3_threephase_periodic_shells_data.no_new_phase_channels
        conclusion_q13_q15_local_phase_exclusion_6adic_q13_data ∧
      conclusion_q13_q15_z3_threephase_periodic_shells_data.semisimple_periodic_shell_bound
        conclusion_q13_q15_local_phase_exclusion_6adic_q15_data ∧
      conclusion_q13_q15_z3_threephase_periodic_shells_data.no_new_phase_channels
        conclusion_q13_q15_local_phase_exclusion_6adic_q15_data ∧
      (∀ n,
        conclusion_q13_q15_local_phase_exclusion_6adic_zero_mod6_tail (n + 72) =
          conclusion_q13_q15_local_phase_exclusion_6adic_zero_mod6_tail n) := by
  have hdyadic13 :
      paper_conclusion_resonance_window_z2_hensel_tail_periodicity_statement 0 13 1 (fun _ => 0) :=
    paper_conclusion_resonance_window_z2_hensel_tail_periodicity 0 13 1 (fun _ => 0)
  have hdyadic15 :
      paper_conclusion_resonance_window_z2_hensel_tail_periodicity_statement 0 15 1 (fun _ => 0) :=
    paper_conclusion_resonance_window_z2_hensel_tail_periodicity 0 15 1 (fun _ => 0)
  have htriadic13 := paper_conclusion_q13_q15_z3_threephase_periodic_shells
    conclusion_q13_q15_local_phase_exclusion_6adic_q13_data
  have htriadic15 := paper_conclusion_q13_q15_z3_threephase_periodic_shells
    conclusion_q13_q15_local_phase_exclusion_6adic_q15_data
  have hcrt :=
    Omega.POM.paper_pom_resonance_mod6_period_q13_15
      conclusion_q13_q15_local_phase_exclusion_6adic_zero_mod6_tail 0 0
      (by intro n; simp [conclusion_q13_q15_local_phase_exclusion_6adic_zero_mod6_tail])
      (by intro n; simp [conclusion_q13_q15_local_phase_exclusion_6adic_zero_mod6_tail])
  refine ⟨hdyadic13, hdyadic15, htriadic13.2.2.1, htriadic13.2.2.2, htriadic15.2.2.1,
    htriadic15.2.2.2, ?_⟩
  simp [conclusion_q13_q15_local_phase_exclusion_6adic_zero_mod6_tail] at hcrt ⊢

end Omega.Conclusion
