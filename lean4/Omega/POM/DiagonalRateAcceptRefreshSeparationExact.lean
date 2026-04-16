import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Chapter-local package for the diagonal accept-refresh construction used to identify the exact
separation distance. The fields record the strong-stationary-time witness, the halting-state
lemma, the exact tail formula read off at the halting state, and the fact that the halting state
always realizes the worst normalized transition ratio. -/
structure DiagonalRateAcceptRefreshSeparationExactData where
  State : Type
  h : State
  sep : Nat → ℝ
  tail : Nat → ℝ
  ratio : State → Nat → ℝ
  strongStationaryTime : Prop
  haltingStateLemma : Prop
  strongStationaryTimeWitness : strongStationaryTime
  haltingStateLemmaWitness : haltingStateLemma
  sep_eq_tail_witness : ∀ m, sep m = tail m
  tail_eq_halting_gap_witness : ∀ m, tail m = 1 - ratio h m
  haltingStateWorst_witness : ∀ y m, ratio h m ≤ ratio y m

/-- Paper-facing exact separation law for the diagonal accept-refresh strong-stationary-time
construction: the strong-stationary-time and halting-state lemmas hold, the separation distance is
exactly the tail probability, and the halting state realizes the worst normalized transition ratio
for every time.
    thm:pom-diagonal-rate-accept-refresh-separation-exact -/
theorem paper_pom_diagonal_rate_accept_refresh_separation_exact
    (D : DiagonalRateAcceptRefreshSeparationExactData) :
    D.strongStationaryTime ∧
      D.haltingStateLemma ∧
      (∀ m, D.sep m = D.tail m) ∧
      (∀ m, D.sep m = 1 - D.ratio D.h m) ∧
      ∀ y m, D.ratio D.h m ≤ D.ratio y m := by
  refine ⟨D.strongStationaryTimeWitness, D.haltingStateLemmaWitness, D.sep_eq_tail_witness, ?_, ?_⟩
  · intro m
    calc
      D.sep m = D.tail m := D.sep_eq_tail_witness m
      _ = 1 - D.ratio D.h m := D.tail_eq_halting_gap_witness m
  · exact D.haltingStateWorst_witness

end Omega.POM
