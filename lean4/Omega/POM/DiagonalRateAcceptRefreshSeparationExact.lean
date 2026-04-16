import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Chapter-local package for the diagonal accept-refresh construction used to identify the exact
separation distance. The fields record the strong-stationary-time witness, the halting-state
lemma, the exact tail formula read off at the halting state, the equivalent survival-probability
presentation, and the fact that the designated worst state is time-independent. -/
structure DiagonalRateAcceptRefreshSeparationExactData where
  State : Type
  h : State
  haltingState : State
  sep : Nat → ℝ
  tail : Nat → ℝ
  survivalProb : Nat → ℝ
  ratio : State → Nat → ℝ
  worstStateRatio : Nat → ℝ
  strongStationaryTime : Prop
  haltingStateLemma : Prop
  worstStateIsMinimizer : Nat → Prop
  strongStationaryTimeWitness : strongStationaryTime
  haltingStateLemmaWitness : haltingStateLemma
  sep_eq_tail_witness : ∀ m, sep m = tail m
  tail_eq_halting_gap_witness : ∀ m, tail m = 1 - ratio h m
  haltingStateWorst_witness : ∀ y m, ratio h m ≤ ratio y m
  sep_le_survivalProb_witness : ∀ m, sep m ≤ survivalProb m
  survivalProb_le_sep_at_halting_witness : ∀ m, survivalProb m ≤ sep m
  worstStateRatio_eq_sep_witness : ∀ m, worstStateRatio m = sep m
  worstStateIsMinimizer_witness : ∀ m, worstStateIsMinimizer m

/-- The accept-refresh strong stationary time is exact: separation equals the tail probability,
the designated halting state attains that value for every time, and so it is a time-independent
worst point. This wrapper keeps both the tail-formula and survival-probability presentations of
`thm:pom-diagonal-rate-accept-refresh-separation-exact`. -/
theorem paper_pom_diagonal_rate_accept_refresh_separation_exact
    (D : DiagonalRateAcceptRefreshSeparationExactData) :
    D.strongStationaryTime ∧
      D.haltingStateLemma ∧
      (∀ m, D.sep m = D.tail m) ∧
      (∀ m, D.sep m = 1 - D.ratio D.h m) ∧
      (∀ y m, D.ratio D.h m ≤ D.ratio y m) ∧
      (∀ m, D.sep m = D.survivalProb m) ∧
      (∀ m, D.worstStateRatio m = D.survivalProb m) ∧
      ∀ m, D.worstStateIsMinimizer m := by
  have hSepEq : ∀ m, D.sep m = D.survivalProb m := by
    intro m
    exact le_antisymm (D.sep_le_survivalProb_witness m)
      (D.survivalProb_le_sep_at_halting_witness m)
  refine ⟨D.strongStationaryTimeWitness, D.haltingStateLemmaWitness, D.sep_eq_tail_witness, ?_, ?_, hSepEq, ?_, D.worstStateIsMinimizer_witness⟩
  · intro m
    calc
      D.sep m = D.tail m := D.sep_eq_tail_witness m
      _ = 1 - D.ratio D.h m := D.tail_eq_halting_gap_witness m
  · exact D.haltingStateWorst_witness
  · intro m
    rw [D.worstStateRatio_eq_sep_witness m, hSepEq m]

end Omega.POM
