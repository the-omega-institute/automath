import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic
import Omega.SPG.BoundaryCycleAuditQueryLowerBound
import Omega.SPG.BoundaryCycleRankFromEntropy

namespace Omega.SPG

open Submodule FiniteDimensional Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- If a zero-transcript query family is complete in the sense that the only linear functional
annihilating every queried cycle is the zero functional, then the number of queries is at least the
cycle-space dimension; combining this with the entropy-to-rank estimate yields the full lower
bound.
    thm:spg-boundary-cycle-audit-query-lower-bound -/
theorem paper_spg_boundary_cycle_audit_query_lower_bound_full
    {r q : ℕ} (hV : finrank K V = r) (z : Fin q → V)
    (spg_boundary_cycle_audit_query_lower_bound_zero_transcript_complete :
      ∀ f : V →ₗ[K] K, (∀ i, f (z i) = 0) → f = 0)
    (n : ℕ) (H A X : ℝ)
    (hlog2 : 0 < Real.log 2)
    (hEntropy : H ≤ 2 * Real.log 2 * (A / (2 : ℝ) ^ n))
    (hRank : A - X + 1 ≤ (r : ℝ)) :
    r ≤ q ∧ (((2 : ℝ) ^ n / (2 * Real.log 2)) * H - X + 1 ≤ q) := by
  have hrq : r ≤ q := by
    by_contra hnot
    have hlt : q < r := Nat.lt_of_not_ge hnot
    have hspan_ne_top : Submodule.span K (Set.range z) ≠ ⊤ :=
      BoundaryCycleAuditQueryLowerBound.paper_spg_boundary_cycle_audit_query_lower_bound hlt hV z
    have hspan_lt_top : Submodule.span K (Set.range z) < ⊤ :=
      lt_of_le_of_ne le_top hspan_ne_top
    obtain ⟨f, hf_nonzero, hf_ker⟩ :=
      Submodule.exists_le_ker_of_lt_top (p := Submodule.span K (Set.range z)) hspan_lt_top
    have hz : ∀ i, f (z i) = 0 := by
      intro i
      exact hf_ker (Submodule.subset_span ⟨i, rfl⟩)
    have hf_zero : f = 0 :=
      spg_boundary_cycle_audit_query_lower_bound_zero_transcript_complete f hz
    exact hf_nonzero hf_zero
  constructor
  · exact hrq
  · have hreal :
        ((2 : ℝ) ^ n / (2 * Real.log 2)) * H - X + 1 ≤ (r : ℝ) :=
      paper_spg_boundary_cycle_rank_from_entropy n H A X r hlog2 hEntropy hRank
    exact hreal.trans (by exact_mod_cast hrq)

end Omega.SPG
