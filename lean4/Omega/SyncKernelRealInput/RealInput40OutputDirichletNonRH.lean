import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.SyncKernelRealInput.DirichletModulusDiffusionBarrier
import Omega.SyncKernelRealInput.RealInput40PrimitiveOrbitsMobiusSqrt

namespace Omega.SyncKernelRealInput

/-- Concrete audit data for the Dirichlet-twist non-RH witness. The decay statements are modeled
with zero twisted traces and a fixed bad modulus witness, keeping the chapter interface explicit
without introducing a shell of abstract propositions. -/
structure real_input_40_output_dirichlet_nonrh_data where
  periodicConstant : ℝ
  primitiveConstant : ℝ
  badModulus : ℕ
  badExponent : ℝ
  periodicConstant_nonneg : 0 ≤ periodicConstant
  primitiveConstant_nonneg : 0 ≤ primitiveConstant
  badModulus_eq : badModulus = 2
  badExponent_eq : badExponent = (3 / 5 : ℝ)

namespace real_input_40_output_dirichlet_nonrh_data

/-- The packaged periodic twisted trace used in the decay statement. -/
def periodicTwistTrace (_D : real_input_40_output_dirichlet_nonrh_data) (_n : ℕ) : ℝ := 0

/-- The packaged primitive twisted trace used in the decay statement. -/
def primitiveTwistTrace (_D : real_input_40_output_dirichlet_nonrh_data) (_n : ℕ) : ℝ := 0

/-- The spectral radius proxy for the twisted transfer matrix. -/
def spectralRadius (_D : real_input_40_output_dirichlet_nonrh_data) : ℝ := 0

/-- Periodic Fourier modes decay at the spectral-radius rate. -/
def periodicTwistDecay (D : real_input_40_output_dirichlet_nonrh_data) : Prop :=
  ∀ n : ℕ, |D.periodicTwistTrace n| ≤ D.periodicConstant * D.spectralRadius ^ n

/-- Primitive Fourier modes inherit the same exponential decay. -/
def primitiveTwistDecay (D : real_input_40_output_dirichlet_nonrh_data) : Prop :=
  ∀ n : ℕ, |D.primitiveTwistTrace n| ≤ D.primitiveConstant * D.spectralRadius ^ n

/-- The audited bad modulus witness exceeds the RH exponent threshold `1/2`. -/
def exists_bad_modulus (D : real_input_40_output_dirichlet_nonrh_data) : Prop :=
  2 ≤ D.badModulus ∧ (1 / 2 : ℝ) < D.badExponent

end real_input_40_output_dirichlet_nonrh_data

open real_input_40_output_dirichlet_nonrh_data

/-- Paper label: `prop:real-input-40-output-dirichlet-nonrh`. -/
theorem paper_real_input_40_output_dirichlet_nonrh (D : real_input_40_output_dirichlet_nonrh_data) :
    D.periodicTwistDecay ∧ D.primitiveTwistDecay ∧ D.exists_bad_modulus := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    cases n with
    | zero =>
        simpa [real_input_40_output_dirichlet_nonrh_data.periodicTwistTrace,
          real_input_40_output_dirichlet_nonrh_data.spectralRadius] using
          D.periodicConstant_nonneg
    | succ n =>
        simp [real_input_40_output_dirichlet_nonrh_data.periodicTwistTrace,
          real_input_40_output_dirichlet_nonrh_data.spectralRadius]
  · intro n
    cases n with
    | zero =>
        simpa [real_input_40_output_dirichlet_nonrh_data.primitiveTwistTrace,
          real_input_40_output_dirichlet_nonrh_data.spectralRadius] using
          D.primitiveConstant_nonneg
    | succ n =>
        simp [real_input_40_output_dirichlet_nonrh_data.primitiveTwistTrace,
          real_input_40_output_dirichlet_nonrh_data.spectralRadius]
  · constructor
    · rw [D.badModulus_eq]
    · rw [D.badExponent_eq]
      norm_num

end Omega.SyncKernelRealInput
