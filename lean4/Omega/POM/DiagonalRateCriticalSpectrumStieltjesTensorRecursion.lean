import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

section DiagonalRateCriticalSpectrumStieltjesTensorRecursion

variable {X Y : Type} [Fintype X] [Fintype Y]

/-- Minimal full-support witness for the chapter-local rational probability weights. -/
def FullSupportProb {α : Type} [Fintype α] (w : α → Rat) : Prop :=
  ∀ a, w a ≠ 0

/-- Chapter-local secular normalization. We keep the rational seed `A = 1`, so the tensor
recursion is carried entirely by the inverse weights. -/
def secularA {α : Type} [Fintype α] (_w : α → Rat) : Rat :=
  1

/-- Chapter-local secular time attached to a single coordinate. -/
def secularTime {α : Type} [Fintype α] (w : α → Rat) (a : α) : Rat :=
  secularA w / w a

/-- Chapter-local Stieltjes transform for the secular times. -/
def stieltjesSecular {α : Type} [Fintype α] (w : α → Rat) (z : Rat) : Rat :=
  ∑ a, 1 / (secularTime w a - z)

/-- Chapter-local `F = 1 - S` secular companion. -/
def stieltjesCompanion {α : Type} [Fintype α] (w : α → Rat) (z : Rat) : Rat :=
  1 - stieltjesSecular w z

/-- Tensor product of two rational weights. -/
def tensorWeight (w : X → Rat) (v : Y → Rat) : X × Y → Rat :=
  fun p => w p.1 * v p.2

/-- The multiplicative secular time on the tensor product. -/
def tensorSecularTime (w : X → Rat) (v : Y → Rat) (p : X × Y) : Rat :=
  secularTime w p.1 * secularTime v p.2

/-- The tensor Stieltjes transform, written as the obvious double sum. -/
def tensorStieltjes (w : X → Rat) (v : Y → Rat) (z : Rat) : Rat :=
  ∑ x, ∑ y, 1 / (tensorSecularTime w v (x, y) - z)

/-- The tensor `F = 1 - S` companion. -/
def tensorCompanion (w : X → Rat) (v : Y → Rat) (z : Rat) : Rat :=
  1 - tensorStieltjes w v z

/-- Chapter-local package for the tensor Stieltjes recursion. -/
def stieltjesTensorRecursionFormula (w : X → Rat) (v : Y → Rat) : Prop :=
  (∀ p : X × Y, secularTime (tensorWeight w v) p = tensorSecularTime w v p) ∧
    ∀ z : Rat,
      tensorStieltjes w v z =
        ∑ x, (1 / secularTime w x) * stieltjesSecular v (z / secularTime w x) ∧
      tensorCompanion w v z =
        1 - ∑ x, (1 / secularTime w x) * (1 - stieltjesCompanion v (z / secularTime w x))

private lemma secularTime_ne_zero {α : Type} [Fintype α] {w : α → Rat}
    (hw : FullSupportProb w) (a : α) : secularTime w a ≠ 0 := by
  simp [secularTime, secularA, hw a]

private lemma secularTime_tensor_eq (w : X → Rat) (v : Y → Rat) (hw : FullSupportProb w)
    (hv : FullSupportProb v) (p : X × Y) :
    secularTime (tensorWeight w v) p = tensorSecularTime w v p := by
  rcases p with ⟨x, y⟩
  let _ := hw
  let _ := hv
  simpa [tensorWeight, tensorSecularTime, secularTime, secularA] using
    (one_div_mul_one_div (w x) (v y)).symm

private lemma tensor_summand_factorization (w : X → Rat) (v : Y → Rat) (hw : FullSupportProb w)
    (x : X) (y : Y) (z : Rat) :
    1 / (tensorSecularTime w v (x, y) - z) =
      (1 / secularTime w x) * (1 / (secularTime v y - z / secularTime w x)) := by
  have hx : secularTime w x ≠ 0 := secularTime_ne_zero hw x
  rw [show tensorSecularTime w v (x, y) - z = secularTime w x * secularTime v y - z by rfl]
  rw [sub_eq_add_neg, add_comm]
  field_simp [hx]
  ring

/-- Paper label: `prop:pom-diagonal-rate-critical-spectrum-stieltjes-tensor-recursion`.
The secular times multiply on tensor products, the Stieltjes double sum factors by `1 / t_x`,
and the `F`-identity is just `F = 1 - S` rewritten after that factorization. -/
theorem paper_pom_diagonal_rate_critical_spectrum_stieltjes_tensor_recursion
    {X Y : Type} [Fintype X] [Fintype Y] (w : X → Rat) (v : Y → Rat) (hw : FullSupportProb w)
    (hv : FullSupportProb v) : stieltjesTensorRecursionFormula w v := by
  refine ⟨fun p => secularTime_tensor_eq w v hw hv p, ?_⟩
  intro z
  have hS :
      tensorStieltjes w v z =
        ∑ x, (1 / secularTime w x) * stieltjesSecular v (z / secularTime w x) := by
    calc
      tensorStieltjes w v z
          = ∑ x, ∑ y, (1 / secularTime w x) * (1 / (secularTime v y - z / secularTime w x)) := by
              refine Finset.sum_congr rfl ?_
              intro x _
              refine Finset.sum_congr rfl ?_
              intro y _
              exact tensor_summand_factorization w v hw x y z
      _ = ∑ x, (1 / secularTime w x) * ∑ y, 1 / (secularTime v y - z / secularTime w x) := by
            refine Finset.sum_congr rfl ?_
            intro x _
            rw [Finset.mul_sum]
      _ = ∑ x, (1 / secularTime w x) * stieltjesSecular v (z / secularTime w x) := by
            refine Finset.sum_congr rfl ?_
            intro x _
            rfl
  refine ⟨?_, ?_⟩
  · exact hS
  · calc
      tensorCompanion w v z = 1 - tensorStieltjes w v z := rfl
      _ = 1 - ∑ x, (1 / secularTime w x) * stieltjesSecular v (z / secularTime w x) := by
            rw [hS]
      _ =
          1 - ∑ x, (1 / secularTime w x) * (1 - stieltjesCompanion v (z / secularTime w x)) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro x _
            simp [stieltjesCompanion]

end DiagonalRateCriticalSpectrumStieltjesTensorRecursion

end Omega.POM
