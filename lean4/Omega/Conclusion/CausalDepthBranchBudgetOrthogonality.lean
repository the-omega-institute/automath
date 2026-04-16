import Mathlib.Tactic

namespace Omega.Conclusion

/-- A fiber of cardinality `d` is exactly distinguishable by a binary auxiliary variable with
    budget `b` when it injects into `2^b` labels. -/
def FiberDistinguishableWithBudget (d b : Nat) : Prop := d ≤ 2 ^ b

/-- Binary branch budget forced by a fiber of cardinality `d`. -/
def fiberBranchBudget (d : Nat) : Nat := Nat.clog 2 d

/-- Exact distinguishability is equivalent to the branch-budget bound `Nat.clog 2 d ≤ b`. -/
theorem fiberBranchBudget_iff_distinguishable (d b : Nat) :
    FiberDistinguishableWithBudget d b ↔ fiberBranchBudget d ≤ b := by
  simpa [FiberDistinguishableWithBudget, fiberBranchBudget] using
    (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).symm

/-- The canonical branch budget realizes exact distinguishability. -/
theorem fiberBranchBudget_distinguishable (d : Nat) :
    FiberDistinguishableWithBudget d (fiberBranchBudget d) := by
  simpa [FiberDistinguishableWithBudget, fiberBranchBudget] using
    (Nat.le_pow_clog (by norm_num : 1 < 2) d)

/-- Abstract expectation operator used to package the pointwise ceiling bounds into an expectation
    sandwich. -/
structure ExpectationWitness (X : Type*) where
  expect : (X → ℝ) → ℝ
  monotone : ∀ {f g : X → ℝ}, (∀ x, f x ≤ g x) → expect f ≤ expect g
  strictMono : ∀ {f g : X → ℝ}, (∀ x, f x < g x) → expect f < expect g
  add_const : ∀ (f : X → ℝ) (c : ℝ), expect (fun x => f x + c) = expect f + c

/-- Chapter-local witness: causal depth is rigidly `3`, each fiber carries a positive size, and
    the ideal logarithmic budget sits strictly between the binary branch budget and that budget
    shifted by `1`. -/
structure CausalDepthBranchBudgetData (X : Type*) where
  causalDepth : Nat
  causalDepth_eq_three : causalDepth = 3
  fiberSize : X → Nat
  fiberSize_pos : ∀ x, 0 < fiberSize x
  idealLogBudget : X → ℝ
  ceilingBounds : ∀ x,
    idealLogBudget x ≤ (fiberBranchBudget (fiberSize x) : ℝ) ∧
      (fiberBranchBudget (fiberSize x) : ℝ) < idealLogBudget x + 1

/-- Paper-facing orthogonality package: the causal-depth rigidity and the fiberwise binary branch
    budget are separate resources, and the pointwise ceiling bounds lift to an expectation
    sandwich.
    thm:conclusion-causal-depth-branch-budget-orthogonality -/
theorem paper_conclusion_causal_depth_branch_budget_orthogonality
    {X : Type*} (E : ExpectationWitness X) (D : CausalDepthBranchBudgetData X) :
    D.causalDepth = 3 ∧
      (∀ x b, FiberDistinguishableWithBudget (D.fiberSize x) b ↔
        fiberBranchBudget (D.fiberSize x) ≤ b) ∧
      (∀ x, FiberDistinguishableWithBudget (D.fiberSize x) (fiberBranchBudget (D.fiberSize x))) ∧
      E.expect D.idealLogBudget ≤ E.expect (fun x => (fiberBranchBudget (D.fiberSize x) : ℝ)) ∧
      E.expect (fun x => (fiberBranchBudget (D.fiberSize x) : ℝ)) <
        E.expect D.idealLogBudget + 1 := by
  refine ⟨D.causalDepth_eq_three, ?_, ?_, ?_, ?_⟩
  · intro x b
    exact fiberBranchBudget_iff_distinguishable (D.fiberSize x) b
  · intro x
    exact fiberBranchBudget_distinguishable (D.fiberSize x)
  · apply E.monotone
    intro x
    exact (D.ceilingBounds x).1
  · have hlt :
        E.expect (fun x => (fiberBranchBudget (D.fiberSize x) : ℝ)) <
          E.expect (fun x => D.idealLogBudget x + 1) := by
      apply E.strictMono
      intro x
      exact (D.ceilingBounds x).2
    calc
      E.expect (fun x => (fiberBranchBudget (D.fiberSize x) : ℝ))
          < E.expect (fun x => D.idealLogBudget x + 1) := hlt
      _ = E.expect D.idealLogBudget + 1 := E.add_const D.idealLogBudget 1

end Omega.Conclusion
