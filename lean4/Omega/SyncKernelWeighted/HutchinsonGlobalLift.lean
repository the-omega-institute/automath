import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Omega.SyncKernelWeighted.PrimitiveSharpPhaseLimit

namespace Omega.SyncKernelWeighted

open scoped BigOperators

noncomputable section

/-- The tensor-product assembly of the single-layer trace data. -/
def hutchinsonTensorAssembly (trace : ℕ → ℝ) (m n : ℕ) : ℝ :=
  (List.replicate m (trace n)).prod

/-- Paper-facing global lift statement: tensor-power assembly matches taking the `m`th power of
the local trace inside the existing Möbius primitive-count formula. -/
def HutchinsonGlobalLiftStatement (m : Nat) : Prop :=
  ∀ (μ trace : ℕ → ℝ) (n : ℕ),
    primitiveSharpMobiusSum μ (hutchinsonTensorAssembly trace m) n =
      ∑ d ∈ n.divisors, μ d * (trace (n / d)) ^ m

private theorem hutchinsonTensorAssembly_eq_pow (trace : ℕ → ℝ) :
    ∀ m n, hutchinsonTensorAssembly trace m n = (trace n) ^ m := by
  intro m
  induction m with
  | zero =>
      intro n
      simp [hutchinsonTensorAssembly]
  | succ m ih =>
      intro n
      simp [hutchinsonTensorAssembly, pow_succ, mul_comm]

/-- Paper label: `prop:hutchinson-global-lift`. The local tensor-product assembly is exactly the
`m`th power of the underlying trace, so the existing primitive Möbius inversion formula lifts
verbatim to the global layered spectrum. -/
theorem paper_hutchinson_global_lift (m : Nat) : HutchinsonGlobalLiftStatement m := by
  intro μ trace n
  unfold primitiveSharpMobiusSum
  refine Finset.sum_congr rfl ?_
  intro d hd
  rw [hutchinsonTensorAssembly_eq_pow trace m (n / d)]

end

end Omega.SyncKernelWeighted
