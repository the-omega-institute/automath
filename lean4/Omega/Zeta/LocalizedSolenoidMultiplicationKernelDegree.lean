import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic
import Omega.Zeta.LocalizedSolenoidCircleQuotientLifts

namespace Omega.Zeta

/-- The finite kernel model attached to multiplication by `n` on the localized solenoid is the
cyclic additive group of order `localizedIndex S n`. -/
abbrev xi_localized_solenoid_multiplication_kernel_degree_kernelModel
    (S : FinitePrimeLocalization) (n : ℕ) :=
  ZMod (localizedIndex S n)

/-- In the simplified localized-solenoid model, the covering degree is the size of the finite
kernel, i.e. the localized quotient index. -/
def xi_localized_solenoid_multiplication_kernel_degree_coverDegree
    (S : FinitePrimeLocalization) (n : ℕ) : ℕ :=
  localizedIndex S n

/-- Paper label: `thm:xi-localized-solenoid-multiplication-kernel-degree`.
For prime multiplication, the localized solenoid admits a unique scalar lift, the localized quotient
ledger computes the kernel size, and the finite kernel is cyclic of that exact order. -/
theorem paper_xi_localized_solenoid_multiplication_kernel_degree
    (S : FinitePrimeLocalization) :
    ∀ ⦃n : ℕ⦄, Nat.Prime n →
      (∃! φ : LocalizedCrossHom S S, localizedCrossHomScalar φ = n) ∧
        ((n ∈ S ↔ localizedIndex S n = 1) ∧ (n ∉ S ↔ localizedIndex S n = n)) ∧
        IsAddCyclic (xi_localized_solenoid_multiplication_kernel_degree_kernelModel S n) ∧
        Nat.card (xi_localized_solenoid_multiplication_kernel_degree_kernelModel S n) =
          xi_localized_solenoid_multiplication_kernel_degree_coverDegree S n := by
  intro n hn
  rcases paper_xi_time_part62db_localized_solenoid_circle_quotient_lifts S n hn with
    ⟨hLift, hIn, hOut⟩
  refine ⟨hLift, ⟨hIn, hOut⟩, inferInstance, ?_⟩
  rw [xi_localized_solenoid_multiplication_kernel_degree_coverDegree]
  exact Nat.card_zmod (localizedIndex S n)

end Omega.Zeta
