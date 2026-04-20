import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic

namespace Omega.EA

open scoped ArithmeticFunction.Moebius

/-- The Adams-twisted primitive numerator attached to the `n`-th primitive contribution. -/
def chebotarevTwistedPrimitiveNumerator
    (B : ℕ → ℕ → ℕ → ℚ) (χ u n : ℕ) : ℚ :=
  (n : ℚ) * B n (χ ^ n) (u ^ n)

/-- The corresponding twisted trace sequence obtained by summing primitive contributions over the
divisors of `n`. -/
noncomputable def chebotarevTwistedTrace
    (B : ℕ → ℕ → ℕ → ℚ) (χ u n : ℕ) : ℚ :=
  ∑ d ∈ n.divisors, chebotarevTwistedPrimitiveNumerator B χ u d

/-- A concrete Möbius-Adams extraction formula: once the twisted trace is expressed as the divisor
sum of Adams-twisted primitive numerators, Möbius inversion recovers the primitive term. This
keeps the divisor reindexing explicit and matches the usual `1 / n` normalization. -/
theorem paper_kernel_chebotarev_mobius_adams
    (B : ℕ → ℕ → ℕ → ℚ) (χ u n : ℕ) (hn : 0 < n) :
    B n (χ ^ n) (u ^ n) =
      (∑ d ∈ n.divisors,
          (ArithmeticFunction.moebius d : ℚ) * chebotarevTwistedTrace B χ u (n / d)) / n := by
  have htrace :
      ∀ m > 0,
        ∑ d ∈ m.divisors, chebotarevTwistedPrimitiveNumerator B χ u d =
          chebotarevTwistedTrace B χ u m := by
    intro m hm
    rfl
  have hmobius :
      ∑ x ∈ n.divisorsAntidiagonal,
        (ArithmeticFunction.moebius x.fst : ℚ) * chebotarevTwistedTrace B χ u x.snd =
          chebotarevTwistedPrimitiveNumerator B χ u n :=
    (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp htrace) n hn
  have hdivisor :
      ∑ d ∈ n.divisors,
        (ArithmeticFunction.moebius d : ℚ) * chebotarevTwistedTrace B χ u (n / d) =
          chebotarevTwistedPrimitiveNumerator B χ u n := by
    rw [← Nat.map_div_right_divisors] at hmobius
    simpa using hmobius
  have hnq : (n : ℚ) ≠ 0 := by
    exact_mod_cast hn.ne'
  rw [hdivisor, chebotarevTwistedPrimitiveNumerator]
  field_simp [hnq]

end Omega.EA
