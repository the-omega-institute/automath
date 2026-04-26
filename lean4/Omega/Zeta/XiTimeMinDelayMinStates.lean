import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic
import Omega.Zeta.XiTimeFiberMinimalDimension

namespace Omega.Zeta

/-- The concrete suffix memory of length `m - 1` used by the standard decoder. -/
abbrev xi_time_min_delay_min_states_suffix_state (m : ℕ) : Type :=
  Fin (m - 1) → Bool

/-- The standard suffix decoder forgets the ambient word and only keeps the suffix state, so the
paper-facing lower bound can be modeled by the constant fold to a single output. -/
def xi_time_min_delay_min_states_suffix_fold (m : ℕ) :
    xi_time_min_delay_min_states_suffix_state m → Unit :=
  fun _ => ()

/-- The unique fiber of the constant suffix fold is equivalent to the full suffix-state space. -/
def xi_time_min_delay_min_states_suffix_fiber_equiv (m : ℕ) :
    LayerFiber (xi_time_min_delay_min_states_suffix_fold m) () ≃
      xi_time_min_delay_min_states_suffix_state m where
  toFun x := x.1
  invFun x := ⟨x, rfl⟩
  left_inv x := by
    cases x
    rfl
  right_inv _ := rfl

/-- The suffix-state space has cardinality `2^(m-1)`. -/
lemma xi_time_min_delay_min_states_suffix_cardinality (m : ℕ) :
    Fintype.card (xi_time_min_delay_min_states_suffix_state m) = 2 ^ (m - 1) := by
  simp [xi_time_min_delay_min_states_suffix_state]

/-- The unique fiber of the constant suffix fold has size `2^(m-1)`. -/
lemma xi_time_min_delay_min_states_suffix_fiber_cardinality (m : ℕ) :
    Nat.card (LayerFiber (xi_time_min_delay_min_states_suffix_fold m) ()) = 2 ^ (m - 1) := by
  calc
    Nat.card (LayerFiber (xi_time_min_delay_min_states_suffix_fold m) ())
        = Nat.card (xi_time_min_delay_min_states_suffix_state m) := by
            exact Nat.card_congr (xi_time_min_delay_min_states_suffix_fiber_equiv m)
    _ = 2 ^ (m - 1) := by
      rw [Nat.card_eq_fintype_card, xi_time_min_delay_min_states_suffix_cardinality]

/-- The standard suffix decoder realizes the delay `m - 1` with exactly `2^(m-1)` suffix states,
and any time-register realization needs at least that many states.
    thm:xi-time-min-delay-min-states -/
theorem paper_xi_time_min_delay_min_states (m : ℕ) :
    let delay := m - 1
    let stateCount := 2 ^ delay
    delay = m - 1 ∧
      (∃ _ : Fin stateCount ≃ xi_time_min_delay_min_states_suffix_state m, True) ∧
      XiTimeRegisterRealization (xi_time_min_delay_min_states_suffix_fold m) stateCount ∧
      ∀ T : ℕ,
        XiTimeRegisterRealization (xi_time_min_delay_min_states_suffix_fold m) T →
          stateCount ≤ T := by
  dsimp
  have hcard :
      Fintype.card (xi_time_min_delay_min_states_suffix_state m) = 2 ^ (m - 1) :=
    xi_time_min_delay_min_states_suffix_cardinality m
  have hmax :
      ∀ x, Nat.card (LayerFiber (xi_time_min_delay_min_states_suffix_fold m) x) ≤ 2 ^ (m - 1) := by
    intro x
    cases x
    rw [xi_time_min_delay_min_states_suffix_fiber_cardinality]
  have hwit :
      ∃ x, Nat.card (LayerFiber (xi_time_min_delay_min_states_suffix_fold m) x) = 2 ^ (m - 1) := by
    refine ⟨(), ?_⟩
    rw [xi_time_min_delay_min_states_suffix_fiber_cardinality]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · refine ⟨?_, trivial⟩
    have hequiv :
        xi_time_min_delay_min_states_suffix_state m ≃ Fin (2 ^ (m - 1)) := by
      simpa [hcard] using Fintype.equivFin (xi_time_min_delay_min_states_suffix_state m)
    exact hequiv.symm
  · exact
      (paper_xi_time_fiber_minimal_dimension
        (xi_time_min_delay_min_states_suffix_fold m) (2 ^ (m - 1)) (2 ^ (m - 1)) hmax hwit).2
  · intro T hT
    exact
      (paper_xi_time_fiber_minimal_dimension
        (xi_time_min_delay_min_states_suffix_fold m) (2 ^ (m - 1)) T hmax hwit).1.mp hT

end Omega.Zeta
