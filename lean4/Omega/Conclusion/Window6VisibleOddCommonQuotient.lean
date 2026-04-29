import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- The concrete three-shell visible odd space with shell labels `2,3,4`. -/
abbrev conclusion_window6_visible_odd_common_quotient_space := Fin 3 → ℂ

/-- The shell-`2` coordinate. -/
def conclusion_window6_visible_odd_common_quotient_shell2
    (f : conclusion_window6_visible_odd_common_quotient_space) : ℂ :=
  f 0

/-- The shell-`3` coordinate. -/
def conclusion_window6_visible_odd_common_quotient_shell3
    (f : conclusion_window6_visible_odd_common_quotient_space) : ℂ :=
  f 1

/-- The shell-`4` coordinate. -/
def conclusion_window6_visible_odd_common_quotient_shell4
    (f : conclusion_window6_visible_odd_common_quotient_space) : ℂ :=
  f 2

/-- The common odd scalar `q_odd(f) = f(4) - f(2)`. -/
def conclusion_window6_visible_odd_common_quotient_q_odd
    (f : conclusion_window6_visible_odd_common_quotient_space) : ℂ :=
  conclusion_window6_visible_odd_common_quotient_shell4 f -
    conclusion_window6_visible_odd_common_quotient_shell2 f

/-- The `O₁` odd visible channel on the three-shell space. -/
def conclusion_window6_visible_odd_common_quotient_O1 :
    conclusion_window6_visible_odd_common_quotient_space →ₗ[ℂ] ℂ where
  toFun f :=
    (conclusion_window6_visible_odd_common_quotient_shell4 f -
        conclusion_window6_visible_odd_common_quotient_shell3 f) +
      (conclusion_window6_visible_odd_common_quotient_shell3 f -
        conclusion_window6_visible_odd_common_quotient_shell2 f)
  map_add' f g := by
    simp [conclusion_window6_visible_odd_common_quotient_shell2,
      conclusion_window6_visible_odd_common_quotient_shell3,
      conclusion_window6_visible_odd_common_quotient_shell4]
    ring
  map_smul' c f := by
    simp [conclusion_window6_visible_odd_common_quotient_shell2,
      conclusion_window6_visible_odd_common_quotient_shell3,
      conclusion_window6_visible_odd_common_quotient_shell4]
    ring

/-- The `O₃` odd visible channel on the three-shell space. -/
def conclusion_window6_visible_odd_common_quotient_O3 :
    conclusion_window6_visible_odd_common_quotient_space →ₗ[ℂ] ℂ where
  toFun f :=
    (conclusion_window6_visible_odd_common_quotient_shell4 f +
        conclusion_window6_visible_odd_common_quotient_shell3 f) -
      (conclusion_window6_visible_odd_common_quotient_shell2 f +
        conclusion_window6_visible_odd_common_quotient_shell3 f)
  map_add' f g := by
    simp [conclusion_window6_visible_odd_common_quotient_shell2,
      conclusion_window6_visible_odd_common_quotient_shell3,
      conclusion_window6_visible_odd_common_quotient_shell4]
    ring
  map_smul' c f := by
    simp [conclusion_window6_visible_odd_common_quotient_shell2,
      conclusion_window6_visible_odd_common_quotient_shell3,
      conclusion_window6_visible_odd_common_quotient_shell4]
    ring

/-- The scalar quotient used by both odd visible channels. -/
abbrev conclusion_window6_visible_odd_common_quotient_common_quotient := ℂ

/-- The common quotient map. -/
def conclusion_window6_visible_odd_common_quotient_q_odd_map :
    conclusion_window6_visible_odd_common_quotient_space →ₗ[ℂ]
      conclusion_window6_visible_odd_common_quotient_common_quotient where
  toFun := conclusion_window6_visible_odd_common_quotient_q_odd
  map_add' f g := by
    simp [conclusion_window6_visible_odd_common_quotient_q_odd,
      conclusion_window6_visible_odd_common_quotient_shell2,
      conclusion_window6_visible_odd_common_quotient_shell4]
    ring
  map_smul' c f := by
    simp [conclusion_window6_visible_odd_common_quotient_q_odd,
      conclusion_window6_visible_odd_common_quotient_shell2,
      conclusion_window6_visible_odd_common_quotient_shell4]
    ring

/-- Paper-facing common-quotient statement for the odd visible channels. -/
def conclusion_window6_visible_odd_common_quotient_statement : Prop :=
  conclusion_window6_visible_odd_common_quotient_O1 =
      conclusion_window6_visible_odd_common_quotient_q_odd_map ∧
    conclusion_window6_visible_odd_common_quotient_O3 =
      conclusion_window6_visible_odd_common_quotient_q_odd_map ∧
    conclusion_window6_visible_odd_common_quotient_O1.ker =
      conclusion_window6_visible_odd_common_quotient_O3.ker ∧
    conclusion_window6_visible_odd_common_quotient_O1.range = ⊤ ∧
    conclusion_window6_visible_odd_common_quotient_O3.range = ⊤ ∧
    Module.finrank ℂ conclusion_window6_visible_odd_common_quotient_common_quotient = 1

/-- Paper label: `thm:conclusion-window6-visible-odd-common-quotient`. On the concrete three-shell
visible odd sector, both channels `O₁` and `O₃` factor through the same scalar
`q_odd(f) = f(4) - f(2)`. Their kernels therefore agree, their common image is the one-dimensional
complex line `ℂ`, and this line serves as the common rank-one quotient. -/
theorem paper_conclusion_window6_visible_odd_common_quotient :
    conclusion_window6_visible_odd_common_quotient_statement := by
  have hO1 :
      conclusion_window6_visible_odd_common_quotient_O1 =
        conclusion_window6_visible_odd_common_quotient_q_odd_map := by
    ext f
    simp [conclusion_window6_visible_odd_common_quotient_O1,
      conclusion_window6_visible_odd_common_quotient_q_odd_map,
      conclusion_window6_visible_odd_common_quotient_q_odd,
      conclusion_window6_visible_odd_common_quotient_shell2,
      conclusion_window6_visible_odd_common_quotient_shell3,
      conclusion_window6_visible_odd_common_quotient_shell4]
  have hO3 :
      conclusion_window6_visible_odd_common_quotient_O3 =
        conclusion_window6_visible_odd_common_quotient_q_odd_map := by
    ext f
    simp [conclusion_window6_visible_odd_common_quotient_O3,
      conclusion_window6_visible_odd_common_quotient_q_odd_map,
      conclusion_window6_visible_odd_common_quotient_q_odd,
      conclusion_window6_visible_odd_common_quotient_shell2,
      conclusion_window6_visible_odd_common_quotient_shell3,
      conclusion_window6_visible_odd_common_quotient_shell4]
  have hsurj :
      Function.Surjective conclusion_window6_visible_odd_common_quotient_q_odd_map := by
    intro z
    refine ⟨fun i => if i = 2 then z else 0, ?_⟩
    simp [conclusion_window6_visible_odd_common_quotient_q_odd_map,
      conclusion_window6_visible_odd_common_quotient_q_odd,
      conclusion_window6_visible_odd_common_quotient_shell2,
      conclusion_window6_visible_odd_common_quotient_shell4]
  have hrange :
      conclusion_window6_visible_odd_common_quotient_q_odd_map.range = ⊤ :=
    LinearMap.range_eq_top.2 hsurj
  refine ⟨hO1, hO3, ?_, ?_, ?_, by simp⟩
  · rw [hO1, hO3]
  · simpa [hO1] using hrange
  · simpa [hO3] using hrange

end

end Omega.Conclusion
