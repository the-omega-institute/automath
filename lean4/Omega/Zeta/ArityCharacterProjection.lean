import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- The explicit `Fin 3` character family used for the first two axes: the zero mode is constant,
and each nonzero mode has total sum zero. -/
def arity3Character (j x : Fin 3) : ℂ :=
  if j = 0 then 1 else (if x = j then 1 else 0) + if x = 0 then (-1 : ℂ) else 0

/-- The explicit `Fin 5` character family used for the third axis. -/
def arity5Character (j x : Fin 5) : ℂ :=
  if j = 0 then 1 else (if x = j then 1 else 0) + if x = 0 then (-1 : ℂ) else 0

@[simp] theorem arity3Character_sum (j : Fin 3) :
    ∑ x, arity3Character j x = if j = 0 then (3 : ℂ) else 0 := by
  fin_cases j <;> simp [arity3Character, Fin.sum_univ_three]

@[simp] theorem arity5Character_sum (j : Fin 5) :
    ∑ x, arity5Character j x = if j = 0 then (5 : ℂ) else 0 := by
  fin_cases j <;> simp [arity5Character, Fin.sum_univ_five]

/-- The explicit inverse-character expansion on the `(3,3,5)` tensor. -/
def arity335CharacterInverseTensor (C : Fin 3 → Fin 3 → Fin 5 → ℂ)
    (a : Fin 3) (b : Fin 3) (c : Fin 5) : ℂ :=
  (1 / 45 : ℂ) *
    ∑ j₁, ∑ j₂, ∑ j₃,
      arity3Character j₁ a * arity3Character j₂ b * arity5Character j₃ c * C j₁ j₂ j₃

/-- Sum over the second and third axes, keeping only the first coordinate. -/
def arity335FirstMarginal (T : Fin 3 → Fin 3 → Fin 5 → ℂ) (a : Fin 3) : ℂ :=
  ∑ b, ∑ c, T a b c

/-- Sum over the first and second axes, keeping only the third coordinate. -/
def arity335ThirdMarginal (T : Fin 3 → Fin 3 → Fin 5 → ℂ) (c : Fin 5) : ℂ :=
  ∑ a, ∑ b, T a b c

/-- The projected first-axis character expansion obtained by killing the marginalized directions. -/
def arity335FirstProjection (C : Fin 3 → Fin 3 → Fin 5 → ℂ) (a : Fin 3) : ℂ :=
  (1 / 3 : ℂ) * ∑ j₁, arity3Character j₁ a * C j₁ 0 0

/-- The projected third-axis character expansion obtained by killing the marginalized directions. -/
def arity335ThirdProjection (C : Fin 3 → Fin 3 → Fin 5 → ℂ) (c : Fin 5) : ℂ :=
  (1 / 5 : ℂ) * ∑ j₃, arity5Character j₃ c * C 0 0 j₃

/-- Marginal summation is exactly character projection for the concrete `(3,3,5)` inverse tensor:
nontrivial frequencies in the summed directions vanish, leaving only the zero-frequency slice.
    lem:arity-character-projection -/
theorem paper_arity_character_projection (C : Fin 3 → Fin 3 → Fin 5 → ℂ) :
    (∀ j : Fin 3, ∑ x, arity3Character j x = if j = 0 then (3 : ℂ) else 0) ∧
    (∀ j : Fin 5, ∑ x, arity5Character j x = if j = 0 then (5 : ℂ) else 0) ∧
    (∀ a, arity335FirstMarginal (arity335CharacterInverseTensor C) a = arity335FirstProjection C a) ∧
    (∀ c, arity335ThirdMarginal (arity335CharacterInverseTensor C) c = arity335ThirdProjection C c) := by
  refine ⟨arity3Character_sum, arity5Character_sum, ?_, ?_⟩
  · intro a
    fin_cases a <;>
      simp [arity335FirstMarginal, arity335CharacterInverseTensor, arity335FirstProjection,
        arity3Character, arity5Character, Fin.sum_univ_three, Fin.sum_univ_five]
      <;> ring_nf
  · intro c
    fin_cases c <;>
      simp [arity335ThirdMarginal, arity335CharacterInverseTensor, arity335ThirdProjection,
        arity3Character, arity5Character, Fin.sum_univ_three, Fin.sum_univ_five]
      <;> ring_nf

end

end Omega.Zeta
