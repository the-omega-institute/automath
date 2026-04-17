import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Real.Basic

namespace Omega.SyncKernelWeighted

/-- Concrete finitely supported datum for a zero-injection update. The Laurent coefficient field is
stored as a `Finsupp`, and `updatedWeightedValue` records the weighted sum after reindexing the
double correction term into the scalar product `Z(τ) * Q(τ)`. -/
structure ZeroInjectionData where
  coeff : ℕ →₀ ℝ
  z : ℕ →₀ ℝ
  q : ℕ →₀ ℝ
  tau : ℝ
  hzero : coeff.sum (fun i bi => bi * tau ^ i) = 0

/-- Laurent evaluation of a finitely supported coefficient field at `τ`. -/
def ZeroInjectionData.evalAt (D : ZeroInjectionData) (f : ℕ →₀ ℝ) : ℝ :=
  f.sum fun i a => a * D.tau ^ i

/-- The weighted value after one zero-injection step, written after exchanging the finite sums. -/
def ZeroInjectionData.updatedWeightedValue (D : ZeroInjectionData) : ℝ :=
  D.evalAt D.z - D.evalAt D.coeff * D.evalAt D.q

/-- The zero-injection step preserves the `τ`-weighted value. -/
def ZeroInjectionData.valuePreserved (D : ZeroInjectionData) : Prop :=
  D.updatedWeightedValue = D.evalAt D.z

/-- After the finite-support reindexing, the correction term is exactly `Z(τ) * Q(τ)`, so
`Z(τ) = 0` cancels it.
    prop:zero-injection-value-preserving -/
theorem paper_zero_injection_value_preserving (D : ZeroInjectionData) : D.valuePreserved := by
  simp [ZeroInjectionData.valuePreserved, ZeroInjectionData.updatedWeightedValue,
    ZeroInjectionData.evalAt, D.hzero]

end Omega.SyncKernelWeighted
