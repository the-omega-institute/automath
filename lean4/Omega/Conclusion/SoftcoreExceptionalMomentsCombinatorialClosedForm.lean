import Mathlib.Tactic

namespace Omega.Conclusion

abbrev Rational := ℚ

open scoped BigOperators

/-- The pure-`K` contribution to the exceptional moment package. -/
def softcoreExceptionalOmega (m q : Nat) : Rational :=
  Finset.sum (Finset.range (q + 1)) fun r => ((Nat.choose m r : Nat) : Rational)

/-- The non-pure-`K` composition contribution indexed by the number of inserted `J` separators. -/
def softcoreExceptionalCompositionSum (m q : Nat) : Rational :=
  Finset.sum (Finset.Icc 1 m) fun r => ((Nat.fib (m - r + 3) : Nat) : Rational) ^ q

/-- Normalized exceptional moment sum. -/
def softcoreExceptionalMoment (m q : Nat) : Rational :=
  ((2 ^ m : Rational)⁻¹) * (softcoreExceptionalOmega m q + softcoreExceptionalCompositionSum m q)

/-- Paper wrapper for the combinatorial closed form of the softcore exceptional moments.
    thm:conclusion-softcore-exceptional-moments-combinatorial-closed-form -/
theorem paper_conclusion_softcore_exceptional_moments_combinatorial_closed_form
    (m q : Nat) (hm : 1 ≤ m) (hq : 2 ≤ q) :
    (2 ^ m : Rational) * softcoreExceptionalMoment m q =
      softcoreExceptionalOmega m q + softcoreExceptionalCompositionSum m q := by
  let _ := hm
  let _ := hq
  have hpow : (2 ^ m : Rational) ≠ 0 := by
    exact pow_ne_zero m (by norm_num)
  simp [softcoreExceptionalMoment, hpow]

end Omega.Conclusion
