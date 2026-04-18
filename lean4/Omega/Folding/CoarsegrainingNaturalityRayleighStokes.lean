import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega

noncomputable section

open scoped BigOperators

/-- The fiber of coarse edges lying above a fixed coarse edge. -/
def coarseEdgeFiber {Ē E : Type*} [Fintype Ē] [DecidableEq E] (ρ : Ē → E) (e : E) : Finset Ē :=
  Finset.univ.filter fun e' => ρ e' = e

/-- The fiber of coarse vertices lying above a fixed coarse vertex. -/
def coarseVertexFiber {VFine V : Type*} [Fintype VFine] [DecidableEq V] (ρ : VFine → V) (v : V) :
    Finset VFine :=
  Finset.univ.filter fun v' => ρ v' = v

/-- Push forward a fine edge-flow by summing over all lifted edges. -/
def coarsePushforward {Ē E : Type*} [Fintype Ē] [DecidableEq E] (ρ : Ē → E) (g : Ē → ℝ) :
    E → ℝ :=
  fun e => Finset.sum (coarseEdgeFiber ρ e) g

/-- Push forward a fine boundary source by summing over lifted vertices. -/
def coarseBoundaryPushforward {VFine V : Type*} [Fintype VFine] [DecidableEq V]
    (ρ : VFine → V) (b : VFine → ℝ) : V → ℝ :=
  fun v => Finset.sum (coarseVertexFiber ρ v) b

/-- The signed Stokes boundary operator on a finite directed multigraph. -/
def stokesBoundary {E V : Type*} [Fintype E] [DecidableEq V] (src dst : E → V) (g : E → ℝ) :
    V → ℝ :=
  fun v =>
    (∑ e : E, if dst e = v then g e else 0) - ∑ e : E, if src e = v then g e else 0

/-- Coarse conductance obtained by summing fine conductances over lifted edges. -/
def coarseConductance {Ē E : Type*} [Fintype Ē] [DecidableEq E] (ρ : Ē → E) (c : Ē → ℝ) :
    E → ℝ :=
  fun e => Finset.sum (coarseEdgeFiber ρ e) c

/-- Rayleigh energy on the fine graph. -/
def fineEnergy {Ē : Type*} [Fintype Ē] (c g : Ē → ℝ) : ℝ :=
  ∑ e' : Ē, g e' ^ 2 / c e'

/-- Rayleigh energy on the coarse graph. -/
def coarseEnergy {Ē E : Type*} [Fintype Ē] [Fintype E] [DecidableEq E] (ρ : Ē → E) (c : Ē → ℝ)
    (g : E → ℝ) : ℝ :=
  ∑ e : E, g e ^ 2 / coarseConductance ρ c e

lemma coarseEnergy_edge_le
    {Ē E : Type*} [Fintype Ē] [Fintype E] [DecidableEq E]
    (ρ : Ē → E) (c g : Ē → ℝ) (hc : ∀ e', 0 < c e') (e : E) :
    (coarsePushforward ρ g e) ^ 2 / coarseConductance ρ c e ≤
      Finset.sum (coarseEdgeFiber ρ e) (fun e' => g e' ^ 2 / c e') := by
  classical
  by_cases hfiber : (coarseEdgeFiber ρ e).Nonempty
  · simpa [coarsePushforward, coarseConductance] using
      (Finset.sq_sum_div_le_sum_sq_div (s := coarseEdgeFiber ρ e) (f := g)
        (hg := fun e' he' => hc e'))
  · have hempty : coarseEdgeFiber ρ e = ∅ := Finset.not_nonempty_iff_eq_empty.mp hfiber
    simp [coarsePushforward, coarseConductance, hempty]

lemma sum_over_coarseEdgeFiber
    {Ē E : Type*} [Fintype Ē] [Fintype E] [DecidableEq E] (ρ : Ē → E) (F : Ē → ℝ) :
    ∑ e : E, Finset.sum (coarseEdgeFiber ρ e) F = ∑ e' : Ē, F e' := by
  classical
  unfold coarseEdgeFiber
  simpa [Finset.sum_filter, Finset.sum_comm]

/-- Aggregating edge-flows preserves total flux. -/
lemma coarsePushforward_sum
    {Ē E : Type*} [Fintype Ē] [Fintype E] [DecidableEq E] (ρ : Ē → E) (g : Ē → ℝ) :
    ∑ e : E, coarsePushforward ρ g e = ∑ e' : Ē, g e' := by
  simpa [coarsePushforward] using sum_over_coarseEdgeFiber ρ g

/-- Aggregating edge-flows preserves total flux and can only decrease the Rayleigh energy after
conductances are pushed forward.
    prop:fold-coarsegraining-naturality-rayleigh-stokes -/
theorem paper_fold_coarsegraining_naturality_rayleigh_stokes :
    ∀ {E EFine : Type*} [Fintype E] [Fintype EFine] [DecidableEq E]
      (ρe : EFine → E) (c g : EFine → ℝ),
      (∀ e', 0 < c e') →
      (∑ e : E, coarsePushforward ρe g e = ∑ e' : EFine, g e') ∧
      coarseEnergy ρe c (coarsePushforward ρe g) ≤ fineEnergy c g := by
  intro E EFine _ _ _ ρe c g hc
  refine ⟨?_, ?_⟩
  · exact coarsePushforward_sum ρe g
  · unfold coarseEnergy fineEnergy
    calc
      ∑ e : E, (coarsePushforward ρe g e) ^ 2 / coarseConductance ρe c e
          ≤ ∑ e : E, Finset.sum (coarseEdgeFiber ρe e) (fun e' => g e' ^ 2 / c e') := by
              refine Finset.sum_le_sum ?_
              intro e _
              exact coarseEnergy_edge_le ρe c g hc e
      _ = ∑ e' : EFine, g e' ^ 2 / c e' :=
        sum_over_coarseEdgeFiber ρe fun e' => g e' ^ 2 / c e'

end

end Omega
