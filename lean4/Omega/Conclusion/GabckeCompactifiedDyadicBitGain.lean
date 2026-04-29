import Omega.CircleDimension.RiemannSiegelGabckeCompactifiedQuadraticGain

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-gabcke-compactified-dyadic-bit-gain`. -/
theorem paper_conclusion_gabcke_compactified_dyadic_bit_gain
    (γ ρ m eK eK1 : ℝ) (hρ : 0 < ρ) (hm : 0 < m) (hleft : 0 ≤ γ - ρ)
    (heK : |eK| ≤ m * ρ) (heK1 : |eK1| ≤ m * ρ) :
    let γK := Omega.CircleDimension.rsGabckeApproxZero γ m eK
    let γK1 := Omega.CircleDimension.rsGabckeApproxZero γ m eK1
    |Omega.CircleDimension.rsGabckeCompactify γK1 -
        Omega.CircleDimension.rsGabckeCompactify γK| ≤
      |eK1 - eK| / (Real.pi * m * (1 + (γ - ρ) ^ 2)) := by
  simpa using
    Omega.CircleDimension.paper_cdim_rs_gabcke_compactified_quadratic_gain γ ρ m eK eK1
      hρ hm hleft heK heK1

end Omega.Conclusion
