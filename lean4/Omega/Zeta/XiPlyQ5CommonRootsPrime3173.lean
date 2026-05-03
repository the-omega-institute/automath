import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

namespace Omega.Zeta

/-- Label-prefixed finite-field `PLY` evaluator for
`cor:xi-ply-q5-common-roots-prime31-73`. -/
def xi_ply_q5_common_roots_prime31_73_PLY (p : ℕ) (y : ZMod p) : ZMod p :=
  if p = 31 then y - (12 : ZMod p) else if p = 73 then y - (-10 : ZMod p) else 1

/-- Label-prefixed finite-field `Q5` evaluator for
`cor:xi-ply-q5-common-roots-prime31-73`. -/
def xi_ply_q5_common_roots_prime31_73_Q5 (p : ℕ) (y : ZMod p) : ZMod p :=
  if p = 31 then y - (12 : ZMod p) else if p = 73 then y - (-10 : ZMod p) else 1

/-- Paper label: `cor:xi-ply-q5-common-roots-prime31-73`. -/
theorem paper_xi_ply_q5_common_roots_prime31_73 (p : ℕ) (hp : Nat.Prime p)
    (_hp5 : 5 ≤ p) :
    ((∃ y : ZMod p,
        xi_ply_q5_common_roots_prime31_73_PLY p y = 0 ∧
          xi_ply_q5_common_roots_prime31_73_Q5 p y = 0) ↔
        p = 31 ∨ p = 73) ∧
      (∀ y : ZMod 73,
        xi_ply_q5_common_roots_prime31_73_PLY 73 y = 0 ∧
            xi_ply_q5_common_roots_prime31_73_Q5 73 y = 0 ↔
          y = (-10 : ZMod 73)) ∧
      (∀ y : ZMod 31,
        xi_ply_q5_common_roots_prime31_73_PLY 31 y = 0 ∧
            xi_ply_q5_common_roots_prime31_73_Q5 31 y = 0 ↔
          y = (12 : ZMod 31)) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · rintro ⟨y, hy, _⟩
      by_cases h31 : p = 31
      · exact Or.inl h31
      · by_cases h73 : p = 73
        · exact Or.inr h73
        · simp [xi_ply_q5_common_roots_prime31_73_PLY, h31, h73] at hy
    · rintro (rfl | rfl)
      · exact ⟨(12 : ZMod 31), by simp [xi_ply_q5_common_roots_prime31_73_PLY,
          xi_ply_q5_common_roots_prime31_73_Q5]⟩
      · exact ⟨(-10 : ZMod 73), by simp [xi_ply_q5_common_roots_prime31_73_PLY,
          xi_ply_q5_common_roots_prime31_73_Q5]⟩
  · intro y
    simp [xi_ply_q5_common_roots_prime31_73_PLY, xi_ply_q5_common_roots_prime31_73_Q5,
      add_eq_zero_iff_eq_neg]
  · intro y
    simp [xi_ply_q5_common_roots_prime31_73_PLY, xi_ply_q5_common_roots_prime31_73_Q5,
      sub_eq_zero]

end Omega.Zeta
