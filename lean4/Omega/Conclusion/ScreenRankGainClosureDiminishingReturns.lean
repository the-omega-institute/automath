import Mathlib.Tactic
import Omega.Conclusion.ScreenAuditGapSupermodularity
import Omega.Conclusion.ScreenAtomicValueAntitone

namespace Omega.Conclusion

open Finset

/-- Corank-style screen cost `λ(S) = ρ - r(S)`. -/
def conclusion_screen_rank_gain_closure_diminishing_returns_lambda
    {α : Type*} [DecidableEq α] (ρ : ℕ) (r : Finset α → ℕ) (S : Finset α) : ℕ :=
  Omega.Conclusion.ScreenAuditGapSupermodularity.AuditGap ρ r S

/-- Gain obtained by adjoining a packet `A`. -/
def conclusion_screen_rank_gain_closure_diminishing_returns_gain
    {α : Type*} [DecidableEq α] (ρ : ℕ) (r : Finset α → ℕ) (S A : Finset α) : ℕ :=
  conclusion_screen_rank_gain_closure_diminishing_returns_lambda ρ r S -
    conclusion_screen_rank_gain_closure_diminishing_returns_lambda ρ r (S ∪ A)

/-- Single-edge gain written as a rank increment. -/
def conclusion_screen_rank_gain_closure_diminishing_returns_single_gain
    {α : Type*} [DecidableEq α] (r : Finset α → ℕ) (S : Finset α) (e : α) : ℕ :=
  r (insert e S) - r S

/-- Closure detected by vanishing corank gain. -/
def conclusion_screen_rank_gain_closure_diminishing_returns_closure
    {α : Type*} [DecidableEq α] (ρ : ℕ) (r : Finset α → ℕ) (S : Finset α) : Set α :=
  {e | conclusion_screen_rank_gain_closure_diminishing_returns_lambda ρ r (insert e S) =
      conclusion_screen_rank_gain_closure_diminishing_returns_lambda ρ r S}

theorem conclusion_screen_rank_gain_closure_diminishing_returns_gain_formula
    {α : Type*} [DecidableEq α] (ρ : ℕ) (r : Finset α → ℕ) (hρ : ∀ s, r s ≤ ρ) :
    ∀ S A,
      conclusion_screen_rank_gain_closure_diminishing_returns_gain ρ r S A =
        r (S ∪ A) - r S := by
  intro S A
  dsimp [conclusion_screen_rank_gain_closure_diminishing_returns_gain,
    conclusion_screen_rank_gain_closure_diminishing_returns_lambda,
    Omega.Conclusion.ScreenAuditGapSupermodularity.AuditGap]
  have hS := hρ S
  have hSA := hρ (S ∪ A)
  omega

theorem conclusion_screen_rank_gain_closure_diminishing_returns_mem_closure_iff
    {α : Type*} [DecidableEq α] (ρ : ℕ) (r : Finset α → ℕ) (hρ : ∀ s, r s ≤ ρ) :
    ∀ S e,
      e ∈ conclusion_screen_rank_gain_closure_diminishing_returns_closure ρ r S ↔
        r (insert e S) = r S := by
  intro S e
  dsimp [conclusion_screen_rank_gain_closure_diminishing_returns_closure,
    conclusion_screen_rank_gain_closure_diminishing_returns_lambda,
    Omega.Conclusion.ScreenAuditGapSupermodularity.AuditGap]
  have hS := hρ S
  have hSe := hρ (insert e S)
  omega

theorem conclusion_screen_rank_gain_closure_diminishing_returns_single_gain_zero_or_one
    {α : Type*} [DecidableEq α] (r : Finset α → ℕ)
    (hmono : ∀ {s t : Finset α}, s ⊆ t → r s ≤ r t)
    (hstep : ∀ s e, r (insert e s) ≤ r s + 1) :
    ∀ S e,
      conclusion_screen_rank_gain_closure_diminishing_returns_single_gain r S e = 0 ∨
        conclusion_screen_rank_gain_closure_diminishing_returns_single_gain r S e = 1 := by
  intro S e
  dsimp [conclusion_screen_rank_gain_closure_diminishing_returns_single_gain]
  have hmono' : r S ≤ r (insert e S) := hmono (subset_insert e S)
  have hstep' := hstep S e
  omega

theorem conclusion_screen_rank_gain_closure_diminishing_returns_single_gain_eq_one_iff
    {α : Type*} [DecidableEq α] (ρ : ℕ) (r : Finset α → ℕ) (hρ : ∀ s, r s ≤ ρ)
    (hmono : ∀ {s t : Finset α}, s ⊆ t → r s ≤ r t)
    (hstep : ∀ s e, r (insert e s) ≤ r s + 1) :
    ∀ S e,
      conclusion_screen_rank_gain_closure_diminishing_returns_single_gain r S e = 1 ↔
        e ∉ conclusion_screen_rank_gain_closure_diminishing_returns_closure ρ r S := by
  intro S e
  have hclosure :=
    conclusion_screen_rank_gain_closure_diminishing_returns_mem_closure_iff ρ r hρ S e
  have hmono' : r S ≤ r (insert e S) := hmono (subset_insert e S)
  have hstep' := hstep S e
  constructor
  · intro hgain hmem
    have heq : r (insert e S) = r S := hclosure.mp hmem
    dsimp [conclusion_screen_rank_gain_closure_diminishing_returns_single_gain] at hgain
    omega
  · intro hnot
    have hneq : r (insert e S) ≠ r S := by
      intro heq
      exact hnot (hclosure.mpr heq)
    dsimp [conclusion_screen_rank_gain_closure_diminishing_returns_single_gain]
    omega

/-- Paper label: `thm:conclusion-screen-rank-gain-closure-diminishing-returns`. -/
theorem paper_conclusion_screen_rank_gain_closure_diminishing_returns {α : Type*}
    [DecidableEq α] (ρ : ℕ) (r : Finset α → ℕ) (hρ : ∀ s, r s ≤ ρ)
    (hmono : ∀ {s t : Finset α}, s ⊆ t → r s ≤ r t)
    (hstep : ∀ s e, r (insert e s) ≤ r s + 1)
    (hsub : ∀ s t, r (s ∩ t) + r (s ∪ t) ≤ r s + r t) :
    (∀ S A,
        conclusion_screen_rank_gain_closure_diminishing_returns_gain ρ r S A =
          r (S ∪ A) - r S) ∧
      (∀ S e,
        conclusion_screen_rank_gain_closure_diminishing_returns_single_gain r S e = 0 ∨
          conclusion_screen_rank_gain_closure_diminishing_returns_single_gain r S e = 1) ∧
      (∀ S e,
        conclusion_screen_rank_gain_closure_diminishing_returns_single_gain r S e = 1 ↔
          e ∉ conclusion_screen_rank_gain_closure_diminishing_returns_closure ρ r S) ∧
      (∀ S e,
        e ∈ conclusion_screen_rank_gain_closure_diminishing_returns_closure ρ r S ↔
          r (insert e S) = r S) ∧
      ∀ {S T : Finset α} {e : α}, S ⊆ T → e ∉ T →
        conclusion_screen_rank_gain_closure_diminishing_returns_single_gain r T e ≤
          conclusion_screen_rank_gain_closure_diminishing_returns_single_gain r S e := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro S A
    exact conclusion_screen_rank_gain_closure_diminishing_returns_gain_formula ρ r hρ S A
  · intro S e
    exact conclusion_screen_rank_gain_closure_diminishing_returns_single_gain_zero_or_one r
      hmono hstep S e
  · intro S e
    exact conclusion_screen_rank_gain_closure_diminishing_returns_single_gain_eq_one_iff ρ r hρ
      hmono hstep S e
  · intro S e
    exact conclusion_screen_rank_gain_closure_diminishing_returns_mem_closure_iff ρ r hρ S e
  · intro S T e hST he
    simpa [conclusion_screen_rank_gain_closure_diminishing_returns_single_gain,
      Omega.Conclusion.ScreenAtomicValueAntitone.MarginalValue] using
      Omega.Conclusion.ScreenAtomicValueAntitone.marginalValue_antitone r hsub hST he

end Omega.Conclusion
