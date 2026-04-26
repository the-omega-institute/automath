import Mathlib.Tactic
import Omega.EA.KernelOneSiteBernoulliClass

namespace Omega.EA

open Polynomial

noncomputable section

/-- The minimal thermo-signature of `K9`: carry-free determinant, first primitive polynomial, and
unbiased endpoint value. -/
def kernelMinimalThermoSignatureK9 : Polynomial ℤ × Polynomial ℤ × ℝ :=
  (globalAssemblyK9Adjacency.charpoly, Polynomial.C 7 + Polynomial.C 14 * Polynomial.X, k9Endpoint)

/-- The minimal thermo-signature of `K13`. -/
def kernelMinimalThermoSignatureK13 : Polynomial ℤ × Polynomial ℤ × ℝ :=
  (globalAssemblyK13Adjacency.charpoly,
    Polynomial.C 3 + Polynomial.C 2 * Polynomial.X + Polynomial.C 2 * Polynomial.X ^ 2 +
      Polynomial.C 6 * Polynomial.X ^ 3,
    k13Endpoint)

/-- The minimal thermo-signature of `K21`. -/
def kernelMinimalThermoSignatureK21 : Polynomial ℤ × Polynomial ℤ × ℝ :=
  (globalAssemblyK21Adjacency.charpoly, Polynomial.C 1 + Polynomial.C 4 * Polynomial.X, k21Endpoint)

/-- Explicit triple package for the three kernel thermo-signatures together with pairwise
separation. -/
def KernelMinimalThermoSignatureThreeStmt : Prop :=
  kernelMinimalThermoSignatureK9 =
      (Polynomial.X - Polynomial.C 7, Polynomial.C 7 + Polynomial.C 14 * Polynomial.X, 21) ∧
    kernelMinimalThermoSignatureK13 =
      (Polynomial.X - Polynomial.C 3,
        Polynomial.C 3 + Polynomial.C 2 * Polynomial.X + Polynomial.C 2 * Polynomial.X ^ 2 +
          Polynomial.C 6 * Polynomial.X ^ 3,
        13) ∧
    kernelMinimalThermoSignatureK21 =
      (Polynomial.X ^ 2 - 3 * Polynomial.X + 1, Polynomial.C 1 + Polynomial.C 4 * Polynomial.X, 5) ∧
    kernelMinimalThermoSignatureK9 ≠ kernelMinimalThermoSignatureK13 ∧
    kernelMinimalThermoSignatureK9 ≠ kernelMinimalThermoSignatureK21 ∧
    kernelMinimalThermoSignatureK13 ≠ kernelMinimalThermoSignatureK21

/-- Paper label: `cor:kernel-minimal-thermo-signature-three`. -/
theorem paper_kernel_minimal_thermo_signature_three : KernelMinimalThermoSignatureThreeStmt := by
  rcases paper_kernel_global_carryfree_spectral_trichotomy with ⟨hK9, hK13, hK21, _, _, _, _⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [kernelMinimalThermoSignatureK9, hK9, k9_endpoint_value]
  · simp [kernelMinimalThermoSignatureK13, hK13, k13Endpoint]
  · simp [kernelMinimalThermoSignatureK21, hK21, k21Endpoint]
  · intro h
    have h' := congrArg (fun s : Polynomial ℤ × Polynomial ℤ × ℝ => s.2.2) h
    norm_num [kernelMinimalThermoSignatureK9, kernelMinimalThermoSignatureK13, k9_endpoint_value,
      k13Endpoint] at h'
  · intro h
    have h' := congrArg (fun s : Polynomial ℤ × Polynomial ℤ × ℝ => s.2.2) h
    norm_num [kernelMinimalThermoSignatureK9, kernelMinimalThermoSignatureK21, k9_endpoint_value,
      k21Endpoint] at h'
  · intro h
    have h' := congrArg (fun s : Polynomial ℤ × Polynomial ℤ × ℝ => s.2.2) h
    norm_num [kernelMinimalThermoSignatureK13, kernelMinimalThermoSignatureK21, k13Endpoint,
      k21Endpoint] at h'

end

end Omega.EA
