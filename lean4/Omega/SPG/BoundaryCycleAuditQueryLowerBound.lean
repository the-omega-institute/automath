import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace Omega.SPG.BoundaryCycleAuditQueryLowerBound

open Submodule FiniteDimensional Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A submodule with strictly smaller `finrank` is not the whole space.
    thm:spg-boundary-cycle-audit-query-lower-bound -/
theorem ne_top_of_finrank_lt (W : Submodule K V)
    (h : finrank K W < finrank K V) : W ≠ ⊤ := by
  intro heq
  rw [heq, finrank_top] at h
  exact lt_irrefl _ h

/-- `q` vectors in an `r`-dimensional space with `q < r` cannot span the whole space.
    thm:spg-boundary-cycle-audit-query-lower-bound -/
theorem paper_spg_boundary_cycle_audit_query_lower_bound
    {r q : ℕ} (hrq : q < r) (hV : finrank K V = r) (z : Fin q → V) :
    Submodule.span K (Set.range z) ≠ ⊤ := by
  apply ne_top_of_finrank_lt
  have hfin : Set.Finite (Set.range z) := Set.finite_range z
  haveI : Fintype (Set.range z) := hfin.fintype
  calc finrank K (Submodule.span K (Set.range z))
      ≤ (Set.range z).toFinset.card := finrank_span_le_card _
    _ = Fintype.card (Set.range z) := by rw [Set.toFinset_card]
    _ ≤ Fintype.card (Fin q) := Fintype.card_range_le z
    _ = q := Fintype.card_fin q
    _ < r := hrq
    _ = finrank K V := hV.symm

end Omega.SPG.BoundaryCycleAuditQueryLowerBound
