import Mathlib.Tactic
import Omega.POM.CouplingExpectationBound

namespace Omega.Kronecker

open Omega.POM.CouplingExpectationBound

structure W1LipschitzPushforwardData where
  α : Type
  couplingCount : ℕ
  Ω : Finset α
  hΩ : 0 < Ω.card
  Φ : ℝ → ℝ
  L : ℝ
  hL : 0 ≤ L
  π : Fin (couplingCount + 1) → α → ℝ × ℝ
  hLipschitz : ∀ x y, |Φ x - Φ y| ≤ L * |x - y|
  best : Fin (couplingCount + 1)
  bestPush : Fin (couplingCount + 1)
  hbest :
    ∀ i,
      expectation Ω (fun ω => |(π best ω).1 - (π best ω).2|) ≤
        expectation Ω (fun ω => |(π i ω).1 - (π i ω).2|)
  hbestPush :
    ∀ i,
      expectation Ω (fun ω => |Φ ((π bestPush ω).1) - Φ ((π bestPush ω).2)|) ≤
        expectation Ω (fun ω => |Φ ((π i ω).1) - Φ ((π i ω).2)|)

noncomputable def W1LipschitzPushforwardData.cost (D : W1LipschitzPushforwardData)
    (i : Fin (D.couplingCount + 1)) : ℝ :=
  expectation D.Ω (fun ω => |(D.π i ω).1 - (D.π i ω).2|)

noncomputable def W1LipschitzPushforwardData.pushforwardCost (D : W1LipschitzPushforwardData)
    (i : Fin (D.couplingCount + 1)) : ℝ :=
  expectation D.Ω (fun ω => |D.Φ ((D.π i ω).1) - D.Φ ((D.π i ω).2)|)

noncomputable def W1LipschitzPushforwardData.w1 (D : W1LipschitzPushforwardData) : ℝ :=
  D.cost D.best

noncomputable def W1LipschitzPushforwardData.pushforwardW1
    (D : W1LipschitzPushforwardData) : ℝ :=
  D.pushforwardCost D.bestPush

def W1LipschitzPushforwardData.pushforwardBound (D : W1LipschitzPushforwardData) : Prop :=
  D.pushforwardW1 ≤ D.L * D.w1

private lemma pushforward_cost_le (D : W1LipschitzPushforwardData) (i : Fin (D.couplingCount + 1)) :
    D.pushforwardCost i ≤ D.L * D.cost i := by
  have hcard_pos : (0 : ℝ) < (D.Ω.card : ℝ) := by
    exact_mod_cast D.hΩ
  have hpoint :
      expectation D.Ω (fun ω => |D.Φ ((D.π i ω).1) - D.Φ ((D.π i ω).2)|) ≤
        expectation D.Ω (fun ω => D.L * |(D.π i ω).1 - (D.π i ω).2|) := by
    unfold expectation
    apply div_le_div_of_nonneg_right ?_ hcard_pos.le
    apply Finset.sum_le_sum
    intro ω hω
    exact D.hLipschitz _ _
  have hscale :
      expectation D.Ω (fun ω => D.L * |(D.π i ω).1 - (D.π i ω).2|) = D.L * D.cost i := by
    unfold W1LipschitzPushforwardData.cost expectation
    rw [← Finset.mul_sum, mul_div_assoc]
  calc
    D.pushforwardCost i
        = expectation D.Ω (fun ω => |D.Φ ((D.π i ω).1) - D.Φ ((D.π i ω).2)|) := rfl
    _ ≤ expectation D.Ω (fun ω => D.L * |(D.π i ω).1 - (D.π i ω).2|) := hpoint
    _ = D.L * D.cost i := hscale

set_option maxHeartbeats 400000 in
/-- A finite coupling-family version of the Lipschitz pushforward `W₁` bound. -/
theorem paper_kronecker_w1_lipschitz_pushforward (D : W1LipschitzPushforwardData) :
    D.pushforwardBound := by
  dsimp [W1LipschitzPushforwardData.pushforwardBound,
    W1LipschitzPushforwardData.pushforwardW1, W1LipschitzPushforwardData.w1]
  exact (D.hbestPush D.best).trans (pushforward_cost_le D D.best)

end Omega.Kronecker
