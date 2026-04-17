import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Core.Word
import Omega.SPG.CoarsegrainedCutFlux

namespace Omega.SPG

open scoped BigOperators

/-- Multiplicative vertex weight attached to the coordinate weights `a`. -/
noncomputable def weight {n : Nat} (a : Fin n → Real) (w : Omega.Word n) : Real :=
  ∏ j, if w j then a j else 1

/-- Outgoing weighted flux across the `i`-cut, measured on the `i = 0` side. -/
noncomputable def weightedCutFluxPos {n : Nat} (i : Fin n) (S : Finset (Omega.Word n))
    (a : Fin n → Real) : Real :=
  ∑ w ∈ Finset.univ.filter (fun w : Omega.Word n => w i = false ∧ w ∈ S ∧ flipAt i w ∉ S),
    weight a w

/-- Incoming weighted flux across the `i`-cut, rewritten on the `i = 0` side by `flipAt`. -/
noncomputable def weightedCutFluxNeg {n : Nat} (i : Fin n) (S : Finset (Omega.Word n))
    (a : Fin n → Real) : Real :=
  ∑ w ∈ Finset.univ.filter (fun w : Omega.Word n => w i = false ∧ w ∉ S ∧ flipAt i w ∈ S),
    weight a (flipAt i w)

/-- Total weight on the `i = 0` layer inside `S`. -/
noncomputable def zeroLayerWeightSum {n : Nat} (i : Fin n) (S : Finset (Omega.Word n))
    (a : Fin n → Real) : Real :=
  ∑ w ∈ Finset.univ.filter (fun w : Omega.Word n => w i = false ∧ w ∈ S), weight a w

/-- Total weight on the `i = 1` layer inside `S`. -/
noncomputable def oneLayerWeightSum {n : Nat} (i : Fin n) (S : Finset (Omega.Word n))
    (a : Fin n → Real) : Real :=
  ∑ w ∈ Finset.univ.filter (fun w : Omega.Word n => w i = false ∧ flipAt i w ∈ S),
    weight a (flipAt i w)

/-- Weight on the paired internal zero-layer vertices. -/
noncomputable def pairedZeroLayerWeightSum {n : Nat} (i : Fin n) (S : Finset (Omega.Word n))
    (a : Fin n → Real) : Real :=
  ∑ w ∈ Finset.univ.filter (fun w : Omega.Word n => w i = false ∧ w ∈ S ∧ flipAt i w ∈ S),
    weight a w

theorem weight_flipAt_of_zero {n : Nat} (i : Fin n) (a : Fin n → Real) (w : Omega.Word n)
    (hwi : w i = false) :
    weight a (flipAt i w) = a i * weight a w := by
  classical
  unfold weight
  have hi : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
  rw [Finset.prod_eq_mul_prod_diff_singleton hi, Finset.prod_eq_mul_prod_diff_singleton hi]
  have hrest :
      ∏ j ∈ Finset.univ \ {i}, (if flipAt i w j then a j else 1) =
        ∏ j ∈ Finset.univ \ {i}, (if w j then a j else 1) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := by
      simpa [Finset.mem_singleton] using hj
    simp [flipAt, Function.update, hji]
  rw [hrest]
  simp [flipAt, hwi, Function.update]

theorem zeroLayerWeightSum_eq_split {n : Nat} (i : Fin n) (S : Finset (Omega.Word n))
    (a : Fin n → Real) :
    zeroLayerWeightSum i S a = weightedCutFluxPos i S a + pairedZeroLayerWeightSum i S a := by
  classical
  simpa [zeroLayerWeightSum, weightedCutFluxPos, pairedZeroLayerWeightSum, Finset.filter_filter,
    Finset.mem_filter, and_assoc, and_left_comm, and_comm] using
    (Finset.sum_filter_add_sum_filter_not
      (s := Finset.univ.filter (fun w : Omega.Word n => w i = false ∧ w ∈ S))
      (p := fun w => flipAt i w ∉ S) (f := fun w => weight a w)).symm

theorem oneLayerWeightSum_eq_split {n : Nat} (i : Fin n) (S : Finset (Omega.Word n))
    (a : Fin n → Real) :
    oneLayerWeightSum i S a =
      (∑ w ∈ Finset.univ.filter (fun w : Omega.Word n => w i = false ∧ w ∈ S ∧ flipAt i w ∈ S),
        weight a (flipAt i w)) +
      weightedCutFluxNeg i S a := by
  classical
  simpa [oneLayerWeightSum, weightedCutFluxNeg, Finset.filter_filter, Finset.mem_filter,
    and_assoc, and_left_comm, and_comm] using
    (Finset.sum_filter_add_sum_filter_not
      (s := Finset.univ.filter (fun w : Omega.Word n => w i = false ∧ flipAt i w ∈ S))
      (p := fun w => w ∈ S) (f := fun w => weight a (flipAt i w))).symm

theorem pairedOneLayerWeightSum_eq {n : Nat} (i : Fin n) (S : Finset (Omega.Word n))
    (a : Fin n → Real) :
    (∑ w ∈ Finset.univ.filter (fun w : Omega.Word n => w i = false ∧ w ∈ S ∧ flipAt i w ∈ S),
      weight a (flipAt i w)) =
      a i * pairedZeroLayerWeightSum i S a := by
  classical
  unfold pairedZeroLayerWeightSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
  rw [weight_flipAt_of_zero i a w hw.1]

/-- Weighted discrete flux identity on the folded hypercube. -/
theorem paper_fold_hypercube_weighted_discrete_flux_identity {n : Nat} (i : Fin n)
    (S : Finset (Omega.Word n)) (a : Fin n -> Real) :
    a i * weightedCutFluxPos i S a - weightedCutFluxNeg i S a =
      a i * zeroLayerWeightSum i S a - oneLayerWeightSum i S a := by
  rw [zeroLayerWeightSum_eq_split, oneLayerWeightSum_eq_split, pairedOneLayerWeightSum_eq]
  ring

end Omega.SPG
