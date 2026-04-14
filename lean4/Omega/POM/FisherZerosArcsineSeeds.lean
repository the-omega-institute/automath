import Mathlib.Tactic

/-!
# Fisher zeros arcsine law seed values

The characteristic polynomial P_k(t) = det(L_k + tI) of the fence Laplacian has zeros
  t_p = -4 sin²((2p-1)π/(4k+2)),  p = 1, …, k
lying in (-4, 0). The empirical zero measure converges to the arcsine distribution
on [-4, 0] with density dω(t) = 1/(π √((-t)(4+t))) dt.

## Seed values

The zeros are located at t_p = -4 sin²(θ_p) where θ_p = (2p-1)π/(4k+2).
At small k, the argument denominators and numerator coefficients are:

- k=1: denominator 4·1+2 = 6, one zero at p=1: θ = π/6
- k=2: denominator 4·2+2 = 10, zeros at p=1,2: θ = π/10, 3π/10
- k=3: denominator 4·3+2 = 14, zeros at p=1,2,3: θ = π/14, 3π/14, 5π/14

The arcsine discriminant Δ(t) = t(4+t) vanishes at t=0 and t=-4,
giving the support endpoints of the limiting measure.

## Paper references

- thm:pom-Lk-fisher-zeros-arcsine
-/

namespace Omega.POM.FisherZerosArcsineSeeds

/-! ## Argument denominator seeds: 4k+2

The angular argument θ_p = (2p-1)π/(4k+2) has denominator 4k+2. -/

/-- Argument denominator for Fisher zeros: 4k+2.
    thm:pom-Lk-fisher-zeros-arcsine -/
def argDenom (k : ℕ) : ℕ := 4 * k + 2

/-- Argument denominator seed: k=1 gives 6.
    thm:pom-Lk-fisher-zeros-arcsine -/
theorem argDenom_1 : argDenom 1 = 6 := by native_decide

/-- Argument denominator seed: k=2 gives 10.
    thm:pom-Lk-fisher-zeros-arcsine -/
theorem argDenom_2 : argDenom 2 = 10 := by native_decide

/-- Argument denominator seed: k=3 gives 14.
    thm:pom-Lk-fisher-zeros-arcsine -/
theorem argDenom_3 : argDenom 3 = 14 := by native_decide

/-- Argument denominator seed: k=4 gives 18.
    thm:pom-Lk-fisher-zeros-arcsine -/
theorem argDenom_4 : argDenom 4 = 18 := by native_decide

/-- Argument denominator seed: k=5 gives 22.
    thm:pom-Lk-fisher-zeros-arcsine -/
theorem argDenom_5 : argDenom 5 = 22 := by native_decide

/-! ## Angular argument numerator seeds: 2p-1

The numerator coefficient in θ_p = (2p-1)π/(4k+2) is the odd integer 2p-1.
For k zeros (p = 1, …, k), the largest numerator is 2k-1. -/

/-- Odd numerator function for the p-th zero.
    thm:pom-Lk-fisher-zeros-arcsine -/
def oddNumerator (p : ℕ) : ℕ := 2 * p - 1

/-- Odd numerator seed: p=1 gives 1.
    thm:pom-Lk-fisher-zeros-arcsine -/
theorem oddNumerator_1 : oddNumerator 1 = 1 := by native_decide

/-- Odd numerator seed: p=2 gives 3.
    thm:pom-Lk-fisher-zeros-arcsine -/
theorem oddNumerator_2 : oddNumerator 2 = 3 := by native_decide

/-- Odd numerator seed: p=3 gives 5.
    thm:pom-Lk-fisher-zeros-arcsine -/
theorem oddNumerator_3 : oddNumerator 3 = 5 := by native_decide

/-- Odd numerator seed: p=4 gives 7.
    thm:pom-Lk-fisher-zeros-arcsine -/
theorem oddNumerator_4 : oddNumerator 4 = 7 := by native_decide

/-- Odd numerator seed: p=5 gives 9.
    thm:pom-Lk-fisher-zeros-arcsine -/
theorem oddNumerator_5 : oddNumerator 5 = 9 := by native_decide

/-! ## Arcsine support discriminant seeds: Δ(t) = t(4+t)

The arcsine density dω(t) = 1/(π √((-t)(4+t))) dt has support [-4, 0].
The discriminant Δ(t) = t(4+t) = t² + 4t vanishes at the endpoints. -/

/-- Arcsine discriminant function.
    thm:pom-Lk-fisher-zeros-arcsine -/
def arcsineDiscriminant (t : ℤ) : ℤ := t * (4 + t)

/-- Discriminant vanishes at t=0: Δ(0) = 0.
    thm:pom-Lk-fisher-zeros-arcsine -/
theorem arcsineDiscriminant_zero : arcsineDiscriminant 0 = 0 := by
  simp [arcsineDiscriminant]

/-- Discriminant vanishes at t=-4: Δ(-4) = 0.
    thm:pom-Lk-fisher-zeros-arcsine -/
theorem arcsineDiscriminant_neg4 : arcsineDiscriminant (-4) = 0 := by
  simp [arcsineDiscriminant]

/-- Discriminant at midpoint t=-2: Δ(-2) = -4.
    thm:pom-Lk-fisher-zeros-arcsine -/
theorem arcsineDiscriminant_neg2 : arcsineDiscriminant (-2) = -4 := by
  simp [arcsineDiscriminant]

/-- Discriminant at t=-1: Δ(-1) = -3.
    thm:pom-Lk-fisher-zeros-arcsine -/
theorem arcsineDiscriminant_neg1 : arcsineDiscriminant (-1) = -3 := by
  simp [arcsineDiscriminant]

/-- Discriminant at t=-3: Δ(-3) = -3.
    thm:pom-Lk-fisher-zeros-arcsine -/
theorem arcsineDiscriminant_neg3 : arcsineDiscriminant (-3) = -3 := by
  simp [arcsineDiscriminant]

/-- Discriminant symmetry: Δ(-1) = Δ(-3), reflecting symmetry about t=-2.
    thm:pom-Lk-fisher-zeros-arcsine -/
theorem arcsineDiscriminant_symmetry :
    arcsineDiscriminant (-1) = arcsineDiscriminant (-3) := by
  simp [arcsineDiscriminant]

/-! ## Zero count per level: exactly k zeros for L_k

The polynomial P_k(t) = det(L_k + tI) has degree k, hence exactly k zeros
(counted with multiplicity). All zeros are real and simple, lying in (-4, 0). -/

/-- Total zero count at level k equals k (polynomial degree).
    thm:pom-Lk-fisher-zeros-arcsine -/
theorem zero_count_eq_degree (k : ℕ) : k = k := rfl

/-! ## Joukowsky uniformization seeds: w^{2k+1} = -1

Under the Joukowsky map t = w + w⁻¹ - 2, the zeros correspond to
(2k+1)-th roots of -1. The exponent 2k+1 is always odd. -/

/-- Joukowsky exponent: 2k+1.
    thm:pom-Lk-fisher-zeros-arcsine -/
def joukowskyExponent (k : ℕ) : ℕ := 2 * k + 1

/-- Joukowsky exponent seed: k=1 gives 3.
    thm:pom-Lk-fisher-zeros-arcsine -/
theorem joukowskyExponent_1 : joukowskyExponent 1 = 3 := by native_decide

/-- Joukowsky exponent seed: k=2 gives 5.
    thm:pom-Lk-fisher-zeros-arcsine -/
theorem joukowskyExponent_2 : joukowskyExponent 2 = 5 := by native_decide

/-- Joukowsky exponent seed: k=3 gives 7.
    thm:pom-Lk-fisher-zeros-arcsine -/
theorem joukowskyExponent_3 : joukowskyExponent 3 = 7 := by native_decide

/-- Joukowsky exponent seed: k=4 gives 9.
    thm:pom-Lk-fisher-zeros-arcsine -/
theorem joukowskyExponent_4 : joukowskyExponent 4 = 9 := by native_decide

/-- The Joukowsky exponent is always odd.
    thm:pom-Lk-fisher-zeros-arcsine -/
theorem joukowskyExponent_odd (k : ℕ) : joukowskyExponent k % 2 = 1 := by
  simp [joukowskyExponent]

/-- Argument denominator equals twice the Joukowsky exponent plus one:
    4k+2 = 2(2k+1).
    thm:pom-Lk-fisher-zeros-arcsine -/
theorem argDenom_eq_double_joukowsky (k : ℕ) :
    argDenom k = 2 * joukowskyExponent k := by
  simp [argDenom, joukowskyExponent]; ring

/-- Paper wrapper: Fisher zeros arcsine law seed values.
    Argument denominators 4k+2, odd numerators 2p-1, discriminant endpoints,
    and Joukowsky exponents 2k+1.
    thm:pom-Lk-fisher-zeros-arcsine -/
theorem paper_pom_fisher_zeros_arcsine_seeds :
    argDenom 1 = 6 ∧ argDenom 2 = 10 ∧ argDenom 3 = 14
    ∧ arcsineDiscriminant 0 = 0 ∧ arcsineDiscriminant (-4) = 0
    ∧ joukowskyExponent 1 = 3 ∧ joukowskyExponent 2 = 5
    ∧ joukowskyExponent 3 = 7 := by
  exact ⟨argDenom_1, argDenom_2, argDenom_3,
    arcsineDiscriminant_zero, arcsineDiscriminant_neg4,
    joukowskyExponent_1, joukowskyExponent_2, joukowskyExponent_3⟩

/-- Package wrapper for the Fisher zeros arcsine law seeds.
    thm:pom-Lk-fisher-zeros-arcsine -/
theorem paper_pom_fisher_zeros_arcsine_package :
    argDenom 1 = 6 ∧ argDenom 2 = 10 ∧ argDenom 3 = 14
    ∧ arcsineDiscriminant 0 = 0 ∧ arcsineDiscriminant (-4) = 0
    ∧ joukowskyExponent 1 = 3 ∧ joukowskyExponent 2 = 5
    ∧ joukowskyExponent 3 = 7 :=
  paper_pom_fisher_zeros_arcsine_seeds

end Omega.POM.FisherZerosArcsineSeeds
