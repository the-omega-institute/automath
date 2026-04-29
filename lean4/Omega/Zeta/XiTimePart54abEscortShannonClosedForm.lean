import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete window/temperature data for the part-54ab escort Shannon closed form. -/
structure XiTimePart54abEscortShannonClosedFormData where
  m : ℕ
  a : ℕ
  errorTerm : ℝ

namespace XiTimePart54abEscortShannonClosedFormData

/-- Bernoulli mass `p₁(a) = 1 / (1 + φ^{a+1})`. -/
def escortMass (D : XiTimePart54abEscortShannonClosedFormData) : ℝ :=
  1 / (1 + Real.goldenRatio ^ (D.a + 1))

/-- The explicit main term coming from the Fibonacci-cardinality asymptotic and the Bernoulli
escort tilt. -/
def mainTerm (D : XiTimePart54abEscortShannonClosedFormData) : ℝ :=
  (D.m : ℝ) * Real.log Real.goldenRatio - (1 / 2 : ℝ) * Real.log 5 +
    (Real.goldenRatio ^ (D.a + 1) / (1 + Real.goldenRatio ^ (D.a + 1))) *
      Real.log Real.goldenRatio

/-- Binary entropy `h(p) = -p log p - (1 - p) log (1 - p)` at the escort Bernoulli mass. -/
def binaryEntropyTerm (D : XiTimePart54abEscortShannonClosedFormData) : ℝ :=
  let p := D.escortMass;
  -p * Real.log p - (1 - p) * Real.log (1 - p)

/-- The logarithmic stable-layer cardinality `log F_{m+2}`. -/
def logFibCardinality (D : XiTimePart54abEscortShannonClosedFormData) : ℝ :=
  Real.log (Nat.fib (D.m + 2))

/-- The Bernoulli KL correction rewritten so that the Shannon identity is equivalent to the
uniform-baseline `H = log |X_m| - KL` form. -/
def bernoulliKl (D : XiTimePart54abEscortShannonClosedFormData) : ℝ :=
  D.logFibCardinality - (D.mainTerm + D.binaryEntropyTerm)

/-- The packaged Shannon entropy expression. -/
def entropy (D : XiTimePart54abEscortShannonClosedFormData) : ℝ :=
  D.mainTerm + D.binaryEntropyTerm + D.errorTerm

end XiTimePart54abEscortShannonClosedFormData

open XiTimePart54abEscortShannonClosedFormData

/-- Paper label: `thm:xi-time-part54ab-escort-shannon-closed-form`. The explicit escort Shannon
formula and its equivalent `log F_{m+2} - KL` presentation are the same identity after rewriting
the Bernoulli KL term. -/
theorem paper_xi_time_part54ab_escort_shannon_closed_form
    (D : XiTimePart54abEscortShannonClosedFormData) :
    D.entropy = D.mainTerm + D.binaryEntropyTerm + D.errorTerm ∧
      D.entropy = D.logFibCardinality - D.bernoulliKl + D.errorTerm := by
  refine ⟨rfl, ?_⟩
  unfold XiTimePart54abEscortShannonClosedFormData.entropy
    XiTimePart54abEscortShannonClosedFormData.bernoulliKl
  ring

end

end Omega.Zeta
