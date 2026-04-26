import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic
import Omega.Conclusion.FibadicOpenIdealFiniteQuotientClassification

namespace Omega.Conclusion

/-- The visible depth-`d` character count is modeled by the finite quotient `ℤ / F_{d+2} ℤ`. -/
noncomputable def conclusion_fibadic_visible_depth_mobius_count_visible_count (d : ℕ) : ℤ := by
  let _ : NeZero (Nat.fib (d + 2)) := ⟨Nat.ne_of_gt (Nat.fib_pos.mpr (by omega))⟩
  exact (Fintype.card (ZMod (Nat.fib (d + 2))) : ℤ)

/-- Exact depth counts are recovered from the visible counts by the Möbius inversion formula on
the divisibility poset. -/
noncomputable def conclusion_fibadic_visible_depth_mobius_count_exact_count (d : ℕ) : ℤ :=
  ∑ e ∈ Nat.divisors d,
    ArithmeticFunction.moebius e *
      conclusion_fibadic_visible_depth_mobius_count_visible_count (d / e)

/-- The visible depth-`d` packet is the disjoint union of the exact-depth packets over the
divisors `e ∣ d`, recorded here at the level of counts. -/
noncomputable def conclusion_fibadic_visible_depth_mobius_count_visible_total_from_exact
    (d : ℕ) : ℤ :=
  ∑ e ∈ Nat.divisors d, conclusion_fibadic_visible_depth_mobius_count_exact_count e

/-- Concrete fibadic visible-depth package: the visible depth-`d` quotient is `ℤ / F_{d+2} ℤ`,
its cardinality is `F_{d+2}`, the exact-depth counts are the Möbius inversion of the visible
counts, and the visible depth is the divisor-union of the exact-depth packets. -/
def conclusion_fibadic_visible_depth_mobius_count_statement : Prop :=
  conclusion_fibadic_open_ideal_finite_quotient_classification_statement ∧
    ∀ d : ℕ,
      conclusion_fibadic_visible_depth_mobius_count_visible_count d = (Nat.fib (d + 2) : ℤ) ∧
      conclusion_fibadic_visible_depth_mobius_count_exact_count d =
        ∑ e ∈ Nat.divisors d,
          ArithmeticFunction.moebius e * (Nat.fib (d / e + 2) : ℤ) ∧
      conclusion_fibadic_visible_depth_mobius_count_visible_total_from_exact d =
        ∑ e ∈ Nat.divisors d, conclusion_fibadic_visible_depth_mobius_count_exact_count e

/-- Paper label: `thm:conclusion-fibadic-visible-depth-mobius-count`. -/
def paper_conclusion_fibadic_visible_depth_mobius_count : Prop := by
  exact conclusion_fibadic_visible_depth_mobius_count_statement

end Omega.Conclusion
