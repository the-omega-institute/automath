import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The audited `18` cyclic window-`6` words, organized as three necklace orbits of length `6`. -/
abbrev conclusion_window6_coxeter_three_necklace_decomposition_word : Type :=
  Fin 3 × Fin 6

/-- The short-root necklace label. -/
def conclusion_window6_coxeter_three_necklace_decomposition_short_root_orbit : Fin 3 := 0

/-- The first long-root necklace label. -/
def conclusion_window6_coxeter_three_necklace_decomposition_long_root_orbit_a : Fin 3 := 1

/-- The second long-root necklace label. -/
def conclusion_window6_coxeter_three_necklace_decomposition_long_root_orbit_b : Fin 3 := 2

/-- The Coxeter action rotates the position inside each necklace and preserves the orbit label. -/
def conclusion_window6_coxeter_three_necklace_decomposition_coxeter :
    conclusion_window6_coxeter_three_necklace_decomposition_word →
      conclusion_window6_coxeter_three_necklace_decomposition_word
  | (orbit, position) => (orbit, position + 1)

/-- Paper-facing finite statement for the window-`6` Coxeter audit: there are `18` cyclic words,
the Coxeter map has order `6`, and the three orbit labels carry the short-root and two long-root
necklaces as explicit `6`-cycles. -/
def conclusion_window6_coxeter_three_necklace_decomposition_statement : Prop :=
  Fintype.card conclusion_window6_coxeter_three_necklace_decomposition_word = 18 ∧
    (∀ w,
      (conclusion_window6_coxeter_three_necklace_decomposition_coxeter^[6]) w = w) ∧
    (∀ position : Fin 6,
      conclusion_window6_coxeter_three_necklace_decomposition_coxeter
          (conclusion_window6_coxeter_three_necklace_decomposition_short_root_orbit, position) =
        (conclusion_window6_coxeter_three_necklace_decomposition_short_root_orbit,
          position + 1)) ∧
    (∀ position : Fin 6,
      conclusion_window6_coxeter_three_necklace_decomposition_coxeter
          (conclusion_window6_coxeter_three_necklace_decomposition_long_root_orbit_a, position) =
        (conclusion_window6_coxeter_three_necklace_decomposition_long_root_orbit_a,
          position + 1)) ∧
    (∀ position : Fin 6,
      conclusion_window6_coxeter_three_necklace_decomposition_coxeter
          (conclusion_window6_coxeter_three_necklace_decomposition_long_root_orbit_b, position) =
        (conclusion_window6_coxeter_three_necklace_decomposition_long_root_orbit_b,
          position + 1)) ∧
    conclusion_window6_coxeter_three_necklace_decomposition_short_root_orbit ≠
      conclusion_window6_coxeter_three_necklace_decomposition_long_root_orbit_a ∧
    conclusion_window6_coxeter_three_necklace_decomposition_short_root_orbit ≠
      conclusion_window6_coxeter_three_necklace_decomposition_long_root_orbit_b ∧
    conclusion_window6_coxeter_three_necklace_decomposition_long_root_orbit_a ≠
      conclusion_window6_coxeter_three_necklace_decomposition_long_root_orbit_b

private theorem conclusion_window6_coxeter_three_necklace_decomposition_coxeter_order_six
    (w : conclusion_window6_coxeter_three_necklace_decomposition_word) :
    (conclusion_window6_coxeter_three_necklace_decomposition_coxeter^[6]) w = w := by
  rcases w with ⟨orbit, position⟩
  fin_cases orbit <;> fin_cases position <;> rfl

/-- Paper label: `thm:conclusion-window6-coxeter-three-necklace-decomposition`. -/
theorem paper_conclusion_window6_coxeter_three_necklace_decomposition :
    conclusion_window6_coxeter_three_necklace_decomposition_statement := by
  refine ⟨by simp [conclusion_window6_coxeter_three_necklace_decomposition_word], ?_, ?_, ?_, ?_,
    by decide, by decide, by decide⟩
  · intro w
    exact conclusion_window6_coxeter_three_necklace_decomposition_coxeter_order_six w
  · intro position
    rfl
  · intro position
    rfl
  · intro position
    rfl

end Omega.Conclusion
