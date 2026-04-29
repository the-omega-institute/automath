import Mathlib.Order.Filter.Basic
import Mathlib.Tactic
import Omega.Conclusion.FibadicVisibleDepthMobiusPrimitiveSemisimplicity

open Filter
open scoped Topology

namespace Omega.Conclusion

/-- Concrete transport data from exact-depth character counts to cyclotomic packet degrees. -/
structure conclusion_fibadic_new_harmonics_dominate_data where
  conclusion_fibadic_new_harmonics_dominate_degPi : Nat → Nat
  conclusion_fibadic_new_harmonics_dominate_exactDepthCount : Nat → Nat
  conclusion_fibadic_new_harmonics_dominate_fib : Nat → Nat
  conclusion_fibadic_new_harmonics_dominate_divisorCount : Nat → Nat
  conclusion_fibadic_new_harmonics_dominate_remainder : Nat → Int
  conclusion_fibadic_new_harmonics_dominate_degPi_eq_exactDepth :
    ∀ d,
      conclusion_fibadic_new_harmonics_dominate_degPi d =
        conclusion_fibadic_new_harmonics_dominate_exactDepthCount d
  conclusion_fibadic_new_harmonics_dominate_exactDepth_asymptotic :
    ∀ d,
      (conclusion_fibadic_new_harmonics_dominate_exactDepthCount d : Int) =
        (conclusion_fibadic_new_harmonics_dominate_fib d : Int) +
          conclusion_fibadic_new_harmonics_dominate_remainder d
  conclusion_fibadic_new_harmonics_dominate_exactDepth_remainder_bound :
    ∀ d,
      Int.natAbs (conclusion_fibadic_new_harmonics_dominate_remainder d) ≤
        conclusion_fibadic_new_harmonics_dominate_divisorCount d *
          Nat.fib (d / 2 + 2)
  conclusion_fibadic_new_harmonics_dominate_exactDepth_ratio_to_one :
    Tendsto
      (fun d : Nat =>
        (conclusion_fibadic_new_harmonics_dominate_exactDepthCount d : Real) /
          (conclusion_fibadic_new_harmonics_dominate_fib d : Real))
      atTop (𝓝 1)

/-- The new cyclotomic packet has the same asymptotic dominance as the exact-depth packet. -/
def conclusion_fibadic_new_harmonics_dominate_statement
    (D : conclusion_fibadic_new_harmonics_dominate_data) : Prop :=
  (∀ d,
    D.conclusion_fibadic_new_harmonics_dominate_degPi d =
      D.conclusion_fibadic_new_harmonics_dominate_exactDepthCount d) ∧
    (∀ d,
      (D.conclusion_fibadic_new_harmonics_dominate_degPi d : Int) =
        (D.conclusion_fibadic_new_harmonics_dominate_fib d : Int) +
          D.conclusion_fibadic_new_harmonics_dominate_remainder d) ∧
    (∀ d,
      Int.natAbs (D.conclusion_fibadic_new_harmonics_dominate_remainder d) ≤
        D.conclusion_fibadic_new_harmonics_dominate_divisorCount d *
          Nat.fib (d / 2 + 2)) ∧
    Tendsto
      (fun d : Nat =>
        (D.conclusion_fibadic_new_harmonics_dominate_degPi d : Real) /
          (D.conclusion_fibadic_new_harmonics_dominate_fib d : Real))
      atTop (𝓝 1)

/-- Paper label: `cor:conclusion-fibadic-new-harmonics-dominate`. -/
theorem paper_conclusion_fibadic_new_harmonics_dominate
    (D : conclusion_fibadic_new_harmonics_dominate_data) :
    conclusion_fibadic_new_harmonics_dominate_statement D := by
  have _hexact := paper_conclusion_fibadic_exact_depth_characters_dominate
  refine ⟨D.conclusion_fibadic_new_harmonics_dominate_degPi_eq_exactDepth, ?_,
    D.conclusion_fibadic_new_harmonics_dominate_exactDepth_remainder_bound, ?_⟩
  · intro d
    rw [D.conclusion_fibadic_new_harmonics_dominate_degPi_eq_exactDepth d]
    exact D.conclusion_fibadic_new_harmonics_dominate_exactDepth_asymptotic d
  · simpa [D.conclusion_fibadic_new_harmonics_dominate_degPi_eq_exactDepth] using
      D.conclusion_fibadic_new_harmonics_dominate_exactDepth_ratio_to_one

end Omega.Conclusion
