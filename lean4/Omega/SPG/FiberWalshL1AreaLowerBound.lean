import Mathlib.Tactic
import Omega.Core.Word
import Omega.SPG.CoarsegrainedCutFlux

namespace Omega.SPG

open scoped BigOperators

universe u

/-- The finite fiber over `x` for a coarse-graining `f`. -/
noncomputable def spgFiber {n : Nat} {X : Type u}
    (f : Omega.Word n → X) (x : X) : Finset (Omega.Word n) :=
  by
    classical
    exact Finset.univ.filter fun ω => f ω = x

/-- The directional fiber bias is the signed cut flux of the `x`-fiber in direction `i`. -/
noncomputable def spgFiberBias {n : Nat} {X : Type u}
    (f : Omega.Word n → X) (i : Fin n) (x : X) : ℝ :=
  by
    classical
    exact ((cutFlux i (spgFiber f x) : ℤ) : ℝ)

/-- The directional boundary count around the `x`-fiber: departures plus arrivals across the
`i`-direction. -/
noncomputable def spgDirectionalBoundaryCount {n : Nat} {X : Type u} [Fintype X]
    (f : Omega.Word n → X) (i : Fin n) (x : X) : ℝ :=
  by
    classical
    exact
      (((Finset.univ.filter
          fun ω : Omega.Word n => ω i = false ∧ f ω = x ∧ f (flipAt i ω) ≠ x).card :
        ℤ) +
        ((Finset.univ.filter
            fun ω : Omega.Word n => ω i = false ∧ f ω ≠ x ∧ f (flipAt i ω) = x).card :
          ℤ) :
        ℝ)

/-- The coordinate-wise crossing-edge count, normalized by the standard factor `1/2` coming from
double counting the two fiber endpoints of each crossing edge. -/
noncomputable def spgCrossingEdgeCount {n : Nat} {X : Type u} [Fintype X]
    (f : Omega.Word n → X) (i : Fin n) : ℝ :=
  by
    classical
    exact (1 / 2 : ℝ) * ∑ x : X, spgDirectionalBoundaryCount f i x

/-- Total SPG boundary area as the sum of directional crossing-edge counts. -/
noncomputable def spgBoundaryArea {n : Nat} {X : Type u} [Fintype X] (f : Omega.Word n → X) : ℝ :=
  by
    classical
    exact ∑ i : Fin n, spgCrossingEdgeCount f i

lemma spgFiberBias_le_directionalBoundaryCount {n : Nat} {X : Type u} [Fintype X]
    (f : Omega.Word n → X) (i : Fin n) (x : X) :
    |spgFiberBias (n := n) (X := X) f i x| ≤
      spgDirectionalBoundaryCount (n := n) (X := X) f i x := by
  classical
  let a : ℝ :=
    (((Finset.univ.filter
        fun ω : Omega.Word n => ω i = false ∧ f ω = x ∧ f (flipAt i ω) ≠ x).card :
      ℤ) :
      ℝ)
  let b : ℝ :=
    (((Finset.univ.filter
        fun ω : Omega.Word n => ω i = false ∧ f ω ≠ x ∧ f (flipAt i ω) = x).card :
      ℤ) :
      ℝ)
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hb : 0 ≤ b := by
    dsimp [b]
    positivity
  have habs : |a - b| ≤ a + b := by
    rw [abs_le]
    constructor <;> linarith
  have hbias : spgFiberBias (n := n) (X := X) f i x = a - b := by
    simp [spgFiberBias, spgFiber, cutFlux, a, b]
  have hboundary : spgDirectionalBoundaryCount (n := n) (X := X) f i x = a + b := by
    simp [spgDirectionalBoundaryCount, a, b]
  rw [hbias, hboundary]
  exact habs

/-- Paper wrapper: the SPG boundary area dominates half of the summed fiberwise first-order Walsh
biases. The local bias is controlled by the directional boundary count, and the factor `1/2`
comes from counting each crossing edge once from each adjacent fiber. -/
theorem paper_spg_fiber_walsh_l1_area_lower_bound
    (n : ℕ) (X : Type) [Fintype X] (f : Omega.Word n → X) :
    spgBoundaryArea (n := n) (X := X) f ≥
      (1 / 2 : ℝ) * ∑ i : Fin n, ∑ x : X, |spgFiberBias (n := n) (X := X) f i x| := by
  classical
  have hdir :
      ∀ i : Fin n,
        ∑ x : X, |spgFiberBias (n := n) (X := X) f i x| ≤
          ∑ x : X, spgDirectionalBoundaryCount (n := n) (X := X) f i x := by
    intro i
    exact Finset.sum_le_sum fun x _ => spgFiberBias_le_directionalBoundaryCount (n := n) (X := X) f i x
  have hsum :
      ∑ i : Fin n, ∑ x : X, |spgFiberBias (n := n) (X := X) f i x| ≤
        ∑ i : Fin n, ∑ x : X, spgDirectionalBoundaryCount (n := n) (X := X) f i x := by
    exact Finset.sum_le_sum fun i _ => hdir i
  have hhalf :
      (1 / 2 : ℝ) * ∑ i : Fin n, ∑ x : X, |spgFiberBias (n := n) (X := X) f i x| ≤
        (1 / 2 : ℝ) * ∑ i : Fin n, ∑ x : X,
          spgDirectionalBoundaryCount (n := n) (X := X) f i x :=
    mul_le_mul_of_nonneg_left hsum (by norm_num)
  have hrewrite :
      (1 / 2 : ℝ) * ∑ i : Fin n, ∑ x : X,
          spgDirectionalBoundaryCount (n := n) (X := X) f i x =
        spgBoundaryArea (n := n) (X := X) f := by
    simp [spgBoundaryArea, spgCrossingEdgeCount, Finset.mul_sum]
  simpa [ge_iff_le] using hhalf.trans_eq hrewrite

end Omega.SPG
