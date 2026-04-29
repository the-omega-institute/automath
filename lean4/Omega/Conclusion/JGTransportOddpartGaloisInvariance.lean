import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-jg-transport-oddpart-galois-invariance`.

If the quotient degree over the intersection divides both the finite `2`-extension tower degree
and an odd intermediate degree, then it is trivial. This is the arithmetic core of the odd-part
Galois invariance argument. -/
theorem paper_conclusion_jg_transport_oddpart_galois_invariance
    (towerHeight oddIntermediateDegree quotientDegree : ℕ)
    (hOddIntermediate : Odd oddIntermediateDegree)
    (hQuotientDyadic : quotientDegree ∣ 2 ^ towerHeight)
    (hQuotientOdd : quotientDegree ∣ oddIntermediateDegree) :
    quotientDegree = 1 := by
  have hCoprime : Nat.Coprime (2 ^ towerHeight) oddIntermediateDegree :=
    Nat.Coprime.pow_left towerHeight hOddIntermediate.coprime_two_left
  have hQuotientGcd :
      quotientDegree ∣ Nat.gcd (2 ^ towerHeight) oddIntermediateDegree :=
    Nat.dvd_gcd hQuotientDyadic hQuotientOdd
  exact Nat.dvd_one.mp (by simpa [hCoprime.gcd_eq_one] using hQuotientGcd)

end Omega.Conclusion
