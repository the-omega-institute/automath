import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic
import Omega.Conclusion.ZGDivisibilitySeriesHardcoreCylinderMass

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `thm:conclusion-zg-ramanujan-shadow-divisor-cylinder-inversion`.
The Ramanujan shadow is the Möbius-weighted divisor transform of the divisibility cylinder
series, the inverse transform recovers the cylinder series, and the existing hardcore-cylinder
mass theorem supplies the final zeta-ratio factorization. -/
theorem paper_conclusion_zg_ramanujan_shadow_divisor_cylinder_inversion
    (R : ℕ → ℚ) (zetaRatio allZeroMass : ℚ) (squarefreeWeight : ℕ → ℚ)
    (hforward : ∀ q,
      R q = ∑ d ∈ Nat.divisors q,
        (ArithmeticFunction.moebius (q / d) : ℚ) * (d : ℚ) *
          (zetaRatio * allZeroMass * squarefreeWeight d))
    (hinverse : ∀ d,
      zetaRatio * allZeroMass * squarefreeWeight d =
        (d : ℚ)⁻¹ * ∑ q ∈ Nat.divisors d, R q) :
    (∀ q,
      R q = ∑ d ∈ Nat.divisors q,
        (ArithmeticFunction.moebius (q / d) : ℚ) * (d : ℚ) *
          (zetaRatio * allZeroMass * squarefreeWeight d)) ∧
    (∀ d,
      zetaRatio * allZeroMass * squarefreeWeight d =
        (d : ℚ)⁻¹ * ∑ q ∈ Nat.divisors d, R q) ∧
    (∀ d,
      let w : ZGHardcoreCylinderWitness :=
        { zetaRatio := zetaRatio, allZeroMass := allZeroMass, squarefreeWeight := squarefreeWeight }
      w.divisibilitySeries d = zetaRatio * w.hardcoreCylinderMass d) := by
  refine ⟨hforward, hinverse, ?_⟩
  intro d
  let w : ZGHardcoreCylinderWitness :=
    { zetaRatio := zetaRatio, allZeroMass := allZeroMass, squarefreeWeight := squarefreeWeight }
  simpa [w] using paper_conclusion_zg_divisibility_series_hardcore_cylinder_mass w d

end Omega.Conclusion
