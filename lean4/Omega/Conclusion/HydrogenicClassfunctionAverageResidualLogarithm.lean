import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Conclusion.HydrogenicResidualAuditCapacity

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

/-- Exact finite conditional-entropy sum for the class-function hydrogenic projection, with
logarithms expressed in base two. -/
def conclusion_hydrogenic_classfunction_average_residual_logarithm_entropy
    (n : ℕ) : ℝ :=
  (1 / (n : ℝ) ^ 2) *
    (Finset.range n).sum fun l =>
      ((2 * l + 1 : ℕ) : ℝ) * (Real.log ((4 * l + 2 : ℕ) : ℝ) / Real.log 2)

/-- The finite midpoint remainder after removing the leading `log₂ n` term. -/
def conclusion_hydrogenic_classfunction_average_residual_logarithm_midpointRemainder
    (n : ℕ) : ℝ :=
  conclusion_hydrogenic_classfunction_average_residual_logarithm_entropy n -
    Real.log (n : ℝ) / Real.log 2

/-- The constant obtained by integrating the midpoint-limit profile
`2x log₂(4x)` on `[0,1]`. -/
def conclusion_hydrogenic_classfunction_average_residual_logarithm_asymptoticConstant :
    ℝ :=
  2 - 1 / (2 * Real.log 2)

/-- Concrete statement for the class-function average residual logarithm: each coarse
class-function fiber has size `4l+2`, the conditional entropy is the advertised finite sum, and
the same sum is packaged as its leading `log₂ n` term plus the finite midpoint remainder. -/
def conclusion_hydrogenic_classfunction_average_residual_logarithm_statement
    (n : ℕ) : Prop :=
  let D : conclusion_hydrogenic_residual_audit_capacity_Data :=
    { conclusion_hydrogenic_residual_audit_capacity_n := n }
  (∀ l : Fin n,
      Fintype.card (conclusion_hydrogenic_residual_audit_capacity_cfFiber D l) =
        4 * l.val + 2) ∧
    conclusion_hydrogenic_classfunction_average_residual_logarithm_entropy n =
      (1 / (n : ℝ) ^ 2) *
        ((Finset.range n).sum fun l =>
          ((2 * l + 1 : ℕ) : ℝ) *
            (Real.log ((4 * l + 2 : ℕ) : ℝ) / Real.log 2)) ∧
    conclusion_hydrogenic_classfunction_average_residual_logarithm_entropy n =
      Real.log (n : ℝ) / Real.log 2 +
        conclusion_hydrogenic_classfunction_average_residual_logarithm_midpointRemainder n ∧
    conclusion_hydrogenic_classfunction_average_residual_logarithm_asymptoticConstant =
      2 - 1 / (2 * Real.log 2)

/-- Paper label: `thm:conclusion-hydrogenic-classfunction-average-residual-logarithm`. -/
theorem paper_conclusion_hydrogenic_classfunction_average_residual_logarithm
    (n : ℕ) (hn : 0 < n) :
    conclusion_hydrogenic_classfunction_average_residual_logarithm_statement n := by
  let D : conclusion_hydrogenic_residual_audit_capacity_Data :=
    { conclusion_hydrogenic_residual_audit_capacity_n := n }
  have _ : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hcapacity := paper_conclusion_hydrogenic_residual_audit_capacity D
  refine ⟨?_, rfl, ?_, rfl⟩
  · intro l
    calc
      Fintype.card (conclusion_hydrogenic_residual_audit_capacity_cfFiber D l) =
          2 * (2 * l.val + 1) := hcapacity.1 l
      _ = 4 * l.val + 2 := by omega
  · unfold conclusion_hydrogenic_classfunction_average_residual_logarithm_midpointRemainder
    ring

end

end Omega.Conclusion
