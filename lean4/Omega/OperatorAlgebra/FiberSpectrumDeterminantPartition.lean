import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Folding.Fiber

namespace Omega.OperatorAlgebra

/-- The determinant potential obtained by multiplying the fiber-spectrum factors
`(1 + t * fiberMultiplicity x)` over `x : X m`. -/
noncomputable def fiberSpectrumDeterminantPotential (m : ℕ) (t : ℝ) : ℝ :=
  ∏ x : Omega.X m, (1 + t * (Omega.X.fiberMultiplicity x : ℝ))

/-- The linear coefficient in the low-temperature expansion of the determinant potential. -/
noncomputable def fiberSpectrumLinearTerm (m : ℕ) : ℕ :=
  ∑ x : Omega.X m, Omega.X.fiberMultiplicity x

/-- The high-temperature logarithmic readout after factoring `t` from every spectral term. -/
noncomputable def fiberSpectrumHighTemperatureReadout (m : ℕ) (t : ℝ) : ℝ :=
  (Fintype.card (Omega.X m) : ℝ) * Real.log t +
    ∑ x : Omega.X m, Real.log ((Omega.X.fiberMultiplicity x : ℝ) + 1 / t)

/-- Chapter-local package for the determinant partition readout: the product formula, the linear
coefficient `2^m`, the Fibonacci cardinality of `X m`, and the high-temperature logarithmic
factorization. -/
def FiberSpectrumDeterminantPartition (m : ℕ) : Prop :=
  fiberSpectrumDeterminantPotential m 0 = 1 ∧
    fiberSpectrumLinearTerm m = 2 ^ m ∧
    Fintype.card (Omega.X m) = Nat.fib (m + 2) ∧
    ∀ {t : ℝ}, 0 < t →
      ∑ x : Omega.X m, Real.log (1 + t * (Omega.X.fiberMultiplicity x : ℝ)) =
        fiberSpectrumHighTemperatureReadout m t

/-- The determinant potential is the product over `x : X m` of `(1 + t * fiberMultiplicity x)`.
Its linear term is `2^m` by `X.fiberMultiplicity_sum_eq_pow`, and factoring `t` from each
summand gives the logarithmic high-temperature readout with the Fibonacci-cardinality factor.
    prop:op-algebra-fiber-spectrum-determinant-partition -/
theorem paper_op_algebra_fiber_spectrum_determinant_partition (m : ℕ) :
    FiberSpectrumDeterminantPartition m := by
  refine ⟨?_, ?_, Omega.X.card_eq_fib m, ?_⟩
  · simp [fiberSpectrumDeterminantPotential]
  · simpa [fiberSpectrumLinearTerm] using Omega.X.fiberMultiplicity_sum_eq_pow m
  · intro t ht
    have ht_ne : t ≠ 0 := ne_of_gt ht
    calc
      ∑ x : Omega.X m, Real.log (1 + t * (Omega.X.fiberMultiplicity x : ℝ))
          = ∑ x : Omega.X m,
              (Real.log t + Real.log ((Omega.X.fiberMultiplicity x : ℝ) + 1 / t)) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              have haux :
                  1 + t * (Omega.X.fiberMultiplicity x : ℝ) =
                    t * ((Omega.X.fiberMultiplicity x : ℝ) + 1 / t) := by
                  field_simp [ht_ne]
                  ring
              rw [haux, Real.log_mul ht_ne (by positivity)]
      _ = ∑ x : Omega.X m, Real.log t +
            ∑ x : Omega.X m, Real.log ((Omega.X.fiberMultiplicity x : ℝ) + 1 / t) := by
              rw [Finset.sum_add_distrib]
      _ = fiberSpectrumHighTemperatureReadout m t := by
              simp [fiberSpectrumHighTemperatureReadout]

end Omega.OperatorAlgebra
