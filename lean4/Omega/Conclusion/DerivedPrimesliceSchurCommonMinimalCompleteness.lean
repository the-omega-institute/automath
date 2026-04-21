import Mathlib.Data.Fintype.Basic
import Omega.POM.ProjectionAsPartitionPrimeRegister
import Omega.Zeta.XiTimePart63cSchurCauchyMasterKernel

namespace Omega.Conclusion

/-- Conclusion-level comparison statement for the shared minimal/completeness principle encoded by
the prime-slice budget theorem and the Schur single-row master kernel. -/
def DerivedPrimesliceSchurCommonMinimalCompletenessStatement (n m : ℕ) : Prop :=
  (∀ S : Finset ℕ,
      (∃ Φ : Omega.POM.Partition n → Omega.POM.PrimeRegisterElement,
          Function.Injective Φ ∧
            (∀ π, Φ π ⊆ S) ∧
            ∀ π σ, Φ (Omega.POM.partitionMeet π σ) = Φ π ∩ Φ σ) →
        Nat.choose n 2 ≤ S.card) ∧
    ∀ {α : Type} [Fintype α] (d : α → ℚ) (y : Fin m → ℚ),
      Omega.Zeta.xiSchurTraceSeries d y = Omega.Zeta.xiSchurCauchyMasterKernel d y ∧
        Omega.Zeta.xiSchurCauchyMasterKernel d y = ∏ j, Omega.Zeta.xiHmKernel d (y j)

/-- Paper label: `thm:derived-primeslice-schur-common-minimal-completeness`. -/
theorem paper_derived_primeslice_schur_common_minimal_completeness
    (n m : ℕ) (hn : 3 ≤ n) : DerivedPrimesliceSchurCommonMinimalCompletenessStatement n m := by
  refine ⟨Omega.POM.paper_pom_meet_gcd_prime_budget n hn, ?_⟩
  intro α _ d y
  simpa using Omega.Zeta.paper_xi_time_part63c_schur_cauchy_master_kernel (d := d) (y := y)

end Omega.Conclusion
