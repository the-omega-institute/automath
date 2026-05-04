import Mathlib.Tactic
import Omega.Zeta.LocalizedSolenoidEndomorphismRing
import Omega.Zeta.LocalizedSolenoidMultiplicationKernelDegree
import Omega.Zeta.LocalizedUnitAutomorphismGroupClassification
import Omega.Zeta.XiLocalizedSolenoidEndomorphismKernelCokernelSfreeNumerator

namespace Omega.Zeta

/-- Paper-facing package for the localized solenoid self-cover classification.  The concrete
components record the scalar endomorphism ring, the explicit `S`-unit automorphisms, the
unit-times-`S`-free numerator reduction, and the finite cyclic kernel/degree ledger for
multiplication self-covers. -/
def xi_localized_solenoid_self_cover_degree_classification_statement
    (S : Omega.Zeta.FinitePrimeLocalization) : Prop :=
  LocalizedSolenoidEndomorphismRing S ∧
    LocalizedUnitAutomorphismGroupClassification S ∧
    (∀ unitPart numerator : ℕ, 0 < unitPart → 0 < numerator →
      xi_localized_solenoid_endomorphism_kernel_cokernel_sfree_numerator_sfreeNumerator
          unitPart numerator = numerator ∧
        Fintype.card
            (xi_localized_solenoid_endomorphism_kernel_cokernel_sfree_numerator_cokernelModel
              numerator) =
          numerator ∧
        Fintype.card
            (xi_localized_solenoid_endomorphism_kernel_cokernel_sfree_numerator_kernelModel
              numerator) =
          numerator ∧
        Nonempty
          (xi_localized_solenoid_endomorphism_kernel_cokernel_sfree_numerator_kernelModel
              numerator ≃
            xi_localized_solenoid_endomorphism_kernel_cokernel_sfree_numerator_cokernelModel
              numerator) ∧
        (xi_localized_solenoid_endomorphism_kernel_cokernel_sfree_numerator_isomorphismCriterion
            numerator ↔
          numerator = 1)) ∧
    (∀ d : ℕ, 0 < d →
      IsAddCyclic (xi_localized_solenoid_multiplication_kernel_degree_kernelModel S d) ∧
        Nat.card (xi_localized_solenoid_multiplication_kernel_degree_kernelModel S d) =
          xi_localized_solenoid_multiplication_kernel_degree_coverDegree S d) ∧
    (∀ ⦃q : ℕ⦄, Nat.Prime q →
      (q ∈ S ↔ localizedIndex S q = 1) ∧
        (q ∉ S ↔ localizedIndex S q = q) ∧
        Nat.card (xi_localized_solenoid_multiplication_kernel_degree_kernelModel S q) =
          xi_localized_solenoid_multiplication_kernel_degree_coverDegree S q)

/-- Paper label: `thm:xi-localized-solenoid-self-cover-degree-classification`. -/
theorem paper_xi_localized_solenoid_self_cover_degree_classification
    (S : Omega.Zeta.FinitePrimeLocalization) :
    xi_localized_solenoid_self_cover_degree_classification_statement S := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact paper_xi_time_part69d_localized_solenoid_endomorphism_ring S
  · exact paper_xi_time_part69_localized_unit_automorphism_group_classification S
  · intro unitPart numerator hunit hnumerator
    exact
      paper_xi_localized_solenoid_endomorphism_kernel_cokernel_sfree_numerator
        unitPart numerator hunit hnumerator
  · intro d hd
    rcases paper_xi_localized_solenoid_finite_subgroups_are_kernels S d hd with
      ⟨hcyclic, hcard⟩
    refine ⟨hcyclic, ?_⟩
    simp [xi_localized_solenoid_multiplication_kernel_degree_coverDegree, hcard]
  · intro q hq
    rcases paper_xi_localized_solenoid_multiplication_kernel_degree S hq with
      ⟨_hlift, hindex, _hcyclic, hcard⟩
    exact ⟨hindex.1, hindex.2, hcard⟩

end Omega.Zeta
