import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- The top exponent of the primitive arity-charge polynomial `P_n(q)`, recorded as the supremum
of the charge statistic over the primitive length-`n` cycles contributing to the coefficient
package. -/
def real_input_40_arity_charge_degree_bound_top_exponent
    {α : Type*} [Fintype α] [DecidableEq α]
    (primitive : α → Prop) [DecidablePred primitive] (chi : α → ℕ) : ℕ :=
  (Finset.univ.filter primitive).sup chi

/-- Paper label: `cor:real-input-40-arity-charge-degree-bound`.
Once the primitive-cycle density audit gives the pointwise estimate
`χ(γ) ≤ ⌊n/2⌋`, the top exponent of `P_n(q)` is bounded by the same quantity. -/
theorem paper_real_input_40_arity_charge_degree_bound
    {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (_hn : 1 ≤ n) (primitive : α → Prop) [DecidablePred primitive] (chi : α → ℕ)
    (hchi : ∀ γ, primitive γ → chi γ ≤ n / 2) :
    real_input_40_arity_charge_degree_bound_top_exponent primitive chi ≤ n / 2 := by
  unfold real_input_40_arity_charge_degree_bound_top_exponent
  refine Finset.sup_le ?_
  intro γ hγ
  exact hchi γ (Finset.mem_filter.mp hγ).2

end Omega.SyncKernelWeighted
