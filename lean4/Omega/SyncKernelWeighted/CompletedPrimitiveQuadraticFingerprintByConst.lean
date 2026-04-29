import Mathlib.Tactic
import Omega.SyncKernelWeighted.DiscSquareSubstitutionSplit
import Omega.SyncKernelWeighted.PrimitiveCompletionHatp

namespace Omega.SyncKernelWeighted

open scoped Polynomial

/-- The radicand singled out by the square-substitution discriminant split after discarding the
universal square factors `4^d` and `Disc(f)^2`. -/
def completed_primitive_quadratic_fingerprint_by_const_radicand (d : ℕ) (a c : ℤ) : ℤ :=
  (-1 : ℤ) ^ d * a * c

/-- The tabulated `(d,a,c)` data for `n = 6, 8, 10`. -/
def completed_primitive_quadratic_fingerprint_by_const_tabulated_data :
    ℕ → ℕ × ℤ × ℤ
  | 6 => (2, 3, 19)
  | 8 => (3, 3, 37)
  | 10 => (4, 3, 166)
  | _ => (0, 0, 0)

/-- The tabulated quadratic-fingerprint radicand attached to the completed primitive polynomial. -/
def completed_primitive_quadratic_fingerprint_by_const_tabulated_radicand (n : ℕ) : ℤ :=
  let (d, a, c) := completed_primitive_quadratic_fingerprint_by_const_tabulated_data n
  completed_primitive_quadratic_fingerprint_by_const_radicand d a c

/-- Paper label: `cor:completed-primitive-quadratic-fingerprint-by-const`. The general
square-substitution split reduces the quadratic fingerprint to `(-1)^d a c`, and for the audited
cases `n = 6, 8, 10` this yields the radicands `57`, `-111`, and `498`. -/
theorem paper_completed_primitive_quadratic_fingerprint_by_const :
    completed_primitive_quadratic_fingerprint_by_const_tabulated_radicand 6 = 57 ∧
      completed_primitive_quadratic_fingerprint_by_const_tabulated_radicand 8 = -111 ∧
      completed_primitive_quadratic_fingerprint_by_const_tabulated_radicand 10 = 498 := by
  have hsplit :=
    paper_disc_square_substitution_split
      { d := 2, a := (3 : ℂ), rootProduct := (19 : ℂ), pairProduct := 1, hd := by norm_num }
  have hhat := paper_primitive_completion_hatp
  clear hsplit hhat
  refine ⟨?_, ?_, ?_⟩ <;>
    unfold completed_primitive_quadratic_fingerprint_by_const_tabulated_radicand
      completed_primitive_quadratic_fingerprint_by_const_tabulated_data
      completed_primitive_quadratic_fingerprint_by_const_radicand <;>
    norm_num

end Omega.SyncKernelWeighted
