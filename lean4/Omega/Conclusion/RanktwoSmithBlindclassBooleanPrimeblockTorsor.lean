import Mathlib.Tactic

namespace Omega.Conclusion

/-- The requested paper theorem is false without the positivity hypothesis `a, b > 0` from the
paper statement: at `(a, b) = (0, 0)` the left-hand side is `0` while the right-hand side is `1`.
-/
theorem paper_conclusion_ranktwo_smith_blindclass_boolean_primeblock_torsor_counterexample :
    let g := Nat.gcd 0 0
    let l := Nat.lcm 0 0
    let h := l / g
    (h.divisors.filter fun u => Nat.Coprime u (h / u)).card ≠ 2 ^ h.primeFactors.card := by
  simp

end Omega.Conclusion
