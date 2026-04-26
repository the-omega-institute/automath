import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Omega.Conclusion.HaltingValuationWalshLedgerUnification

namespace Omega.DerivedConsequences

open Omega.Conclusion

/-- The fixed-resolution observer only records whether the common halting scale `L * N` has fallen
below the chosen resolution. -/
def derived_halting_resolution_localfactor_synchronization_resolution_observation
    (L m : ℕ)
    (σ : paper_derived_halting_valuation_walsh_ledger_unification_halting_state) : ℕ :=
  match σ with
  | .diverges => 0
  | .haltsAt N => if m ≤ L * N then 0 else 1

/-- The local-factor side records the exponential error barrier attached to the same halting time
`N`. -/
noncomputable def derived_halting_resolution_localfactor_synchronization_localfactor_error
    (σ : paper_derived_halting_valuation_walsh_ledger_unification_halting_state) : ℝ :=
  match σ with
  | .diverges => 0
  | .haltsAt N => (1 / 2 : ℝ) ^ N

lemma derived_halting_resolution_localfactor_synchronization_finite_resolution_blindness
    (L m N : ℕ) (hm : m ≤ L * N) :
    derived_halting_resolution_localfactor_synchronization_resolution_observation L m
        (.haltsAt N) =
      derived_halting_resolution_localfactor_synchronization_resolution_observation L m
        .diverges := by
  simp [derived_halting_resolution_localfactor_synchronization_resolution_observation, hm]

lemma derived_halting_resolution_localfactor_synchronization_localfactor_barrier (N : ℕ) :
    derived_halting_resolution_localfactor_synchronization_localfactor_error (.haltsAt N) ≤
      (1 / 2 : ℝ) ^ N := by
  simp [derived_halting_resolution_localfactor_synchronization_localfactor_error]

/-- Paper label: `prop:derived-halting-resolution-localfactor-synchronization`.
The same halting time `N` simultaneously controls the finite-resolution blind spot and the
exponential local-factor error barrier. -/
theorem paper_derived_halting_resolution_localfactor_synchronization (L m : ℕ) (hL : 0 < L) :
    ∀ σ : paper_derived_halting_valuation_walsh_ledger_unification_halting_state,
      match σ with
      | .diverges =>
          derived_halting_resolution_localfactor_synchronization_resolution_observation L m σ = 0 ∧
            derived_halting_resolution_localfactor_synchronization_localfactor_error σ = 0
      | .haltsAt N =>
          (m ≤ L * N →
              derived_halting_resolution_localfactor_synchronization_resolution_observation L m σ =
                derived_halting_resolution_localfactor_synchronization_resolution_observation L m
                  .diverges) ∧
            paper_derived_halting_valuation_walsh_ledger_unification_valuation_depth L σ =
              some (L * N) ∧
            paper_derived_halting_valuation_walsh_ledger_unification_walsh_breakpoint L σ =
              some (L * N + 1) ∧
            derived_halting_resolution_localfactor_synchronization_localfactor_error σ ≤
              (1 / 2 : ℝ) ^ N := by
  intro σ
  cases σ with
  | diverges =>
      simp [derived_halting_resolution_localfactor_synchronization_resolution_observation,
        derived_halting_resolution_localfactor_synchronization_localfactor_error]
  | haltsAt N =>
      have hsync :=
        paper_derived_halting_valuation_walsh_ledger_unification L hL
          (paper_derived_halting_valuation_walsh_ledger_unification_halting_state.haltsAt N)
      rcases hsync.2.2.2 with ⟨_, hdepth, hbreak, _, _, _, _⟩
      refine ⟨?_, hdepth, hbreak, ?_⟩
      · intro hm
        exact
          derived_halting_resolution_localfactor_synchronization_finite_resolution_blindness
            L m N hm
      · exact
          derived_halting_resolution_localfactor_synchronization_localfactor_barrier N

end Omega.DerivedConsequences
