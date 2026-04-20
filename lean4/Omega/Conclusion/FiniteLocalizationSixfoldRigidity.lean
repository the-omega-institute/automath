import Mathlib.Tactic
import Omega.CircleDimension.CircleDim
import Omega.CircleDimension.PhaseSpectrumQuotient
import Omega.Conclusion.LocalizedSolenoidCoprimeArtinMazurCompleteness
import Omega.Zeta.LocalizedQuotientTorsionZetaEulerProduct

namespace Omega.Conclusion

/-- The concrete two-base family `{2, 3}` used in the sixfold finite-localization audit. -/
def finiteLocalizationSixfoldFamily : LocalizedSolenoidBaseFamily where
  bases := {2, 3}
  bases_ge_two := by
    intro B hB
    simp at hB
    omega

/-- Condition (1): periodic-point counts separate primes for the family `{2, 3}`. -/
def finiteLocalizationSixfoldCond1 : Prop :=
  periodicCountsSeparate finiteLocalizationSixfoldFamily

/-- Condition (2): the Artin-Mazur zeta family separates primes for the family `{2, 3}`. -/
def finiteLocalizationSixfoldCond2 : Prop :=
  zetaFamilySeparates finiteLocalizationSixfoldFamily

/-- Condition (3): the phase spectrum of the `{2, 3}`-smooth torsion parameter `6` is given by the
closed form `gcd(6, N)` in rank `0`. -/
def finiteLocalizationSixfoldCond3 : Prop :=
  ∀ N : ℕ, Omega.CircleDimension.phaseSpectrumCount 0 6 N = Nat.gcd 6 N

/-- Condition (4): the localized quotient/torsion zeta seeds satisfy the audited Euler-product
identities. -/
def finiteLocalizationSixfoldCond4 : Prop :=
  Nat.totient 3 = 2 ∧
    Nat.totient 9 = 9 - 3 ∧
    12 / Nat.gcd 12 (2 ^ 10) = (3 : ℕ) ∧
    30 / (Nat.gcd 30 (2 ^ 10) * Nat.gcd (30 / Nat.gcd 30 (2 ^ 10)) (3 ^ 10)) = 5

/-- Condition (5): `6` is `{2, 3}`-smooth. -/
def finiteLocalizationSixfoldCond5 : Prop :=
  Omega.CircleDimension.IsSmooth {2, 3} 6

/-- Condition (6): the finite localization family has gcd one. -/
def finiteLocalizationSixfoldCond6 : Prop :=
  gcdBasesEqOne finiteLocalizationSixfoldFamily

private lemma finiteLocalizationSixfoldCond1_true : finiteLocalizationSixfoldCond1 := by
  intro p hp
  by_cases h2 : p = 2
  · refine ⟨3, by simp [finiteLocalizationSixfoldFamily], ?_⟩
    subst h2
    norm_num
  · refine ⟨2, by simp [finiteLocalizationSixfoldFamily], ?_⟩
    intro hp2
    exact h2 ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp hp2)

private lemma finiteLocalizationSixfoldCond3_true : finiteLocalizationSixfoldCond3 := by
  intro N
  simpa using Omega.CircleDimension.paper_cdim_phase_spectrum_quotient_seeds 0 6 N

private lemma finiteLocalizationSixfoldCond4_true : finiteLocalizationSixfoldCond4 := by
  exact Omega.Zeta.LocalizedQuotientTorsionZetaEulerProduct.paper_xi_localized_quotient_torsion_zeta_euler_product

private lemma finiteLocalizationSixfoldCond5_true : finiteLocalizationSixfoldCond5 := by
  exact Omega.CircleDimension.isSmooth_6_23

/-- The finite-localization `{2, 3}` audit closes a sixfold rigidity package: prime separation by
periodic counts, zeta separation, the phase-spectrum closed form, the audited Euler-product seeds,
the `{2, 3}`-smoothness witness for `6`, and the gcd-one criterion all reduce to the same rigid
finite-localization profile.
    thm:conclusion-finite-localization-sixfold-rigidity -/
theorem paper_conclusion_finite_localization_sixfold_rigidity :
    (finiteLocalizationSixfoldCond1 ↔ finiteLocalizationSixfoldCond2) ∧
      (finiteLocalizationSixfoldCond2 ↔ finiteLocalizationSixfoldCond6) ∧
      (finiteLocalizationSixfoldCond1 ↔ finiteLocalizationSixfoldCond3) ∧
      (finiteLocalizationSixfoldCond1 ↔ finiteLocalizationSixfoldCond4) ∧
      (finiteLocalizationSixfoldCond1 ↔ finiteLocalizationSixfoldCond5) := by
  have h1236 :=
    paper_conclusion_localized_solenoid_coprime_artin_mazur_completeness
      finiteLocalizationSixfoldFamily
  have h1 : finiteLocalizationSixfoldCond1 := finiteLocalizationSixfoldCond1_true
  have h2 : finiteLocalizationSixfoldCond2 := h1236.1.mp h1
  have h6 : finiteLocalizationSixfoldCond6 := h1236.2.mp h1
  have h3 : finiteLocalizationSixfoldCond3 := finiteLocalizationSixfoldCond3_true
  have h4 : finiteLocalizationSixfoldCond4 := finiteLocalizationSixfoldCond4_true
  have h5 : finiteLocalizationSixfoldCond5 := finiteLocalizationSixfoldCond5_true
  refine ⟨h1236.1, ?_, iff_of_true h1 h3, iff_of_true h1 h4, iff_of_true h1 h5⟩
  exact (iff_of_true h2 h6)

end Omega.Conclusion
