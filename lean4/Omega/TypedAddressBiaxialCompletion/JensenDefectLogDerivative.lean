import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.HorizonPurityRepulsion
import Omega.TypedAddressBiaxialCompletion.JensenDefectFiniteization

namespace Omega.TypedAddressBiaxialCompletion

/-- Concrete data for the Jensen-defect log-derivative interface. The structure keeps the actual
defect function, its zero-free predicate, the verified finiteization semantics, and the
first-derivative law needed to differentiate the repulsion radius. -/
structure JensenDefectLogDerivativeData where
  defect : ℝ → ℝ
  zeroFree : ℝ → Prop
  defectDerivative : ℝ → ℝ
  finiteizationSemantics :
      ∀ rho : ℝ, 0 < rho → rho < 1 ->
        0 ≤ defect rho ∧ (defect rho = 0 ↔ zeroFree rho)
  defect_hasDerivAt :
      ∀ {rho : ℝ}, 0 < rho → rho < 1 -> HasDerivAt defect (defectDerivative rho) rho

namespace JensenDefectLogDerivativeData

/-- The finite-radius Jensen-defect package induced by the log-derivative data. -/
def toJensenDefectFiniteizationData (D : JensenDefectLogDerivativeData) :
    JensenDefectFiniteizationData where
  defect := D.defect
  zeroFree := D.zeroFree
  semantics := D.finiteizationSemantics

/-- The derivative of the repulsion radius along the defect profile. -/
noncomputable def repulsionDerivative (D : JensenDefectLogDerivativeData) (rho : ℝ) : ℝ :=
  Real.exp (-D.defect rho) * (1 - rho * D.defectDerivative rho)

theorem repulsionRadius_hasDerivAt (D : JensenDefectLogDerivativeData)
    {rho : ℝ} (hrho : 0 < rho) (hrho_lt : rho < 1) :
    HasDerivAt (fun t => repulsionRadius t (D.defect t)) (D.repulsionDerivative rho) rho := by
  have hExp :
      HasDerivAt (fun t => Real.exp (-D.defect t))
        (Real.exp (-D.defect rho) * (-D.defectDerivative rho)) rho := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      ((Real.hasDerivAt_exp (-D.defect rho)).comp rho ((D.defect_hasDerivAt hrho hrho_lt).neg))
  have hProd :
      HasDerivAt (fun t => t * Real.exp (-D.defect t))
        (1 * Real.exp (-D.defect rho) +
          rho * (Real.exp (-D.defect rho) * (-D.defectDerivative rho))) rho := by
    simpa using (hasDerivAt_id rho).mul hExp
  have hFormula :
      1 * Real.exp (-D.defect rho) +
          rho * (Real.exp (-D.defect rho) * (-D.defectDerivative rho)) =
        D.repulsionDerivative rho := by
    unfold repulsionDerivative
    ring
  rw [hFormula] at hProd
  simpa [repulsionRadius] using hProd

end JensenDefectLogDerivativeData

open JensenDefectLogDerivativeData

/-- Publication-facing log-derivative package: the finite-radius Jensen-defect semantics from the
existing finiteization wrapper are exported together with the verified defect derivative law and
the induced derivative formula for the repulsion radius. -/
def jensenDefectLogDerivativeStatement (D : JensenDefectLogDerivativeData) : Prop :=
  (∀ {rho : ℝ}, 0 < rho → rho < 1 →
      0 ≤ D.defect rho ∧ (D.defect rho = 0 ↔ D.zeroFree rho)) ∧
    (∀ {rho : ℝ}, 0 < rho → rho < 1 → HasDerivAt D.defect (D.defectDerivative rho) rho) ∧
    (∀ {rho : ℝ}, 0 < rho → rho < 1 →
      HasDerivAt (fun t => repulsionRadius t (D.defect t)) (D.repulsionDerivative rho) rho)

/-- The typed-address Jensen-defect log-derivative interface packages the finiteization law, the
defect derivative, and the induced repulsion-radius derivative into one theorem.
    prop:typed-address-biaxial-completion-jensen-defect-log-derivative -/
theorem paper_typed_address_biaxial_completion_jensen_defect_log_derivative
    (D : JensenDefectLogDerivativeData) : jensenDefectLogDerivativeStatement D := by
  refine ⟨?_, ?_, ?_⟩
  · intro rho hrho hrho_lt
    exact D.finiteizationSemantics rho hrho hrho_lt
  · intro rho hrho hrho_lt
    exact D.defect_hasDerivAt hrho hrho_lt
  · intro rho hrho hrho_lt
    exact D.repulsionRadius_hasDerivAt hrho hrho_lt

end Omega.TypedAddressBiaxialCompletion
