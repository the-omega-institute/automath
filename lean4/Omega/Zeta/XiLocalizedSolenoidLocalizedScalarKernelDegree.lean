import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic
import Omega.Zeta.LocalizedSolenoidMultiplicationKernelDegree
import Omega.Zeta.LocalizedUnitAutomorphismGroupClassification

namespace Omega.Zeta

/-- The `S`-free numerator ledger for a localized scalar in the finite solenoid model. -/
def xi_localized_solenoid_localized_scalar_kernel_degree_sfreePart
    (S : FinitePrimeLocalization) (a : ℕ) : ℕ :=
  localizedIndex S a

/-- The localized scalar represented by a unit coordinate times an integer numerator. -/
noncomputable def xi_localized_solenoid_localized_scalar_kernel_degree_scalar
    (S : FinitePrimeLocalization) (u : LocalizedUnitCoordinates S) (a : ℕ) : ℚ :=
  localizedUnitScalar S u * a

/-- The scalar kernel is transferred through the localized unit to the integer kernel of the
stripped `S`-free numerator. -/
abbrev xi_localized_solenoid_localized_scalar_kernel_degree_kernelModel
    (S : FinitePrimeLocalization) (_u : LocalizedUnitCoordinates S) (a : ℕ) :=
  xi_localized_solenoid_multiplication_kernel_degree_kernelModel S
    (xi_localized_solenoid_localized_scalar_kernel_degree_sfreePart S a)

/-- The covering degree of localized scalar multiplication is the stripped numerator. -/
def xi_localized_solenoid_localized_scalar_kernel_degree_coverDegree
    (S : FinitePrimeLocalization) (a : ℕ) : ℕ :=
  xi_localized_solenoid_localized_scalar_kernel_degree_sfreePart S a

lemma xi_localized_solenoid_localized_scalar_kernel_degree_sfreePart_idempotent
    (S : FinitePrimeLocalization) (a : ℕ) :
    xi_localized_solenoid_localized_scalar_kernel_degree_sfreePart S
        (xi_localized_solenoid_localized_scalar_kernel_degree_sfreePart S a) =
      xi_localized_solenoid_localized_scalar_kernel_degree_sfreePart S a := by
  unfold xi_localized_solenoid_localized_scalar_kernel_degree_sfreePart localizedIndex nSperp
  by_cases haS : a ∈ S
  · simp [haS]
  · simp [haS]

/-- Paper label: `thm:xi-localized-solenoid-localized-scalar-kernel-degree`.
In the localized finite model, multiplying by a localized unit does not change the finite kernel;
after the unit factor is stripped, the kernel and covering degree are exactly those of integer
multiplication by the `S`-free numerator. -/
theorem paper_xi_localized_solenoid_localized_scalar_kernel_degree
    (S : FinitePrimeLocalization) (u : LocalizedUnitCoordinates S) (a : ℕ) (ha : 0 < a) :
    denominatorSupportedBy S
        (xi_localized_solenoid_localized_scalar_kernel_degree_scalar S u a) ∧
      xi_localized_solenoid_localized_scalar_kernel_degree_scalar S u a ≠ 0 ∧
      IsAddCyclic (xi_localized_solenoid_localized_scalar_kernel_degree_kernelModel S u a) ∧
      Nat.card (xi_localized_solenoid_localized_scalar_kernel_degree_kernelModel S u a) =
        xi_localized_solenoid_localized_scalar_kernel_degree_coverDegree S a ∧
      Nonempty
        (xi_localized_solenoid_localized_scalar_kernel_degree_kernelModel S u a ≃+
          xi_localized_solenoid_multiplication_kernel_degree_kernelModel S
            (xi_localized_solenoid_localized_scalar_kernel_degree_sfreePart S a)) ∧
      (xi_localized_solenoid_localized_scalar_kernel_degree_coverDegree S a = 1 ↔
        xi_localized_solenoid_localized_scalar_kernel_degree_sfreePart S a = 1) := by
  rcases paper_xi_time_part69_localized_unit_automorphism_group_classification S with
    ⟨hunit, _hcoords⟩
  rcases hunit u with ⟨huSupp, huNonzero, _huInvSupp, _σ, _hσ⟩
  have haNonzero : ((a : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt ha
  refine ⟨?_, ?_, inferInstance, ?_, ⟨AddEquiv.refl _⟩, Iff.rfl⟩
  · exact denominatorSupportedBy_mul huSupp (denominatorSupportedBy_intCast S a)
  · unfold xi_localized_solenoid_localized_scalar_kernel_degree_scalar
    exact mul_ne_zero huNonzero haNonzero
  · rw [Nat.card_zmod, xi_localized_solenoid_localized_scalar_kernel_degree_coverDegree]
    exact xi_localized_solenoid_localized_scalar_kernel_degree_sfreePart_idempotent S a

end Omega.Zeta
