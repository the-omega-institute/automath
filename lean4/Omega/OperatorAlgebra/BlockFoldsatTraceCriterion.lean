import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldPushforwardLift

namespace Omega.OperatorAlgebra

open FoldPushforwardLiftData

local instance boolPredCoe {α : Type*} : CoeFun (α → Bool) (fun _ => α → Prop) where
  coe f := fun a => f a = true

/-- Paper label: `prop:block-foldsat-trace-criterion`.
The accepted-microstate indicator has nonzero trace on the fiber exactly when the fiber contains
an accepted lift, and its pushforward is the accepted-cardinality itself. -/
theorem paper_block_foldsat_trace_criterion (D : Omega.OperatorAlgebra.FoldPushforwardLiftData)
    (accept : D.Ω → Bool) (x : D.X) :
    (0 < ((D.fiber x).filter accept).card ↔ ∃ a ∈ D.fiber x, accept a) ∧
      D.pushforward (fun a => if accept a then (1 : ℚ) else 0) x =
        (((D.fiber x).filter accept).card : ℚ) := by
  refine ⟨?_, ?_⟩
  · constructor
    · intro h
      rcases Finset.card_pos.mp h with ⟨a, ha⟩
      exact ⟨a, by simpa using ha⟩
    · rintro ⟨a, ha, haccept⟩
      exact Finset.card_pos.mpr ⟨a, by simp [ha, haccept]⟩
  · calc
      D.pushforward (fun a => if accept a then (1 : ℚ) else 0) x
          = Finset.sum ((D.fiber x).filter accept) (fun _ => (1 : ℚ)) := by
              simp [FoldPushforwardLiftData.pushforward]
      _ = (((D.fiber x).filter accept).card : ℚ) := by
            simp

end Omega.OperatorAlgebra
