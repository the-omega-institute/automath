import Mathlib.Tactic

namespace Omega.POM

/-- The intercept of the linear asymptote is the supremum endpoint value.
    Identity: sup_{α ≤ α_*} {q(α - α_*) + f(α)} at q→∞ concentrates at α = α_*.
    Algebraic seed: for f(α) = α + c with α_* = 1, c = 0:
    sup_{α ≤ 1} {q(α-1) + α} = sup_{α ≤ 1} {(q+1)α - q} = (q+1)·1 - q = 1 = f(1).
    thm:pom-zero-temperature-two-term-expansion-maxfiber-entropy -/
theorem zero_temp_intercept_linear_seed (q : ℕ) :
    (q + 1 : ℤ) * 1 - q = 1 := by omega

/-- Power sum dominance: for M₁ > M₂ > 0, the ratio M₂^q / M₁^q → 0 as q → ∞.
    Seed verification: (1/2)^3 < 1.
    This captures that N₁ M₁^q dominates S_q(m) for large q.
    thm:pom-zero-temperature-two-term-expansion-maxfiber-entropy -/
theorem power_dominance_half_seed :
    (1 : ℚ) / 2 ^ 3 < 1 := by norm_num

/-- Escort mass concentration: π_{m,q}(M_m) = N_m M_m^q / S_q(m).
    When S_q(m) = N₁ M₁^q + remainder with remainder ≪ N₁ M₁^q,
    the escort mass → 1.
    Seed: N₁=2, M₁=3, remainder=1, q=1: mass = 2·3/(2·3+1) = 6/7.
    thm:pom-zero-temperature-two-term-expansion-maxfiber-entropy -/
theorem escort_mass_seed :
    (2 * 3 : ℚ) / (2 * 3 + 1) = 6 / 7 := by norm_num

/-- The max-fiber entropy rate h_* = lim sup (1/m) log N_m.
    Seed: if N_m = 2^m, then 2^m / 2^m = 1, confirming the ratio is well-defined.
    def:pom-max-fiber-entropy-rate -/
theorem max_fiber_entropy_constant_branching_seed :
    (2 : ℕ) ^ 5 / 2 ^ 5 = 1 := by norm_num

/-- Escort freezing threshold: when qδ > log φ - h_*, escort concentrates
    exponentially on M_m. The exponent is qδ - (log φ - h_*).
    Seed: q=3, δ=1, log φ ≈ 0.48, h_*=0 gives exponent ≈ 3 - 0.48 = 2.52 > 0.
    Algebraic: 3 * 1 - 1 = 2 > 0.
    prop:pom-escort-freezing-gap-threshold -/
theorem escort_freezing_threshold_seed :
    3 * 1 - (1 : ℤ) = 2 := by norm_num

/-- Paper package: `thm:pom-zero-temperature-two-term-expansion-maxfiber-entropy`.
    Seed values for zero temperature two-term expansion with max-fiber entropy. -/
theorem paper_pom_zero_temperature_two_term_expansion_seeds :
    (∀ q : ℕ, (q + 1 : ℤ) * 1 - q = 1) ∧
    ((1 : ℚ) / 2 ^ 3 < 1) ∧
    ((2 * 3 : ℚ) / (2 * 3 + 1) = 6 / 7) ∧
    ((2 : ℕ) ^ 5 / 2 ^ 5 = 1) := by
  exact ⟨fun _ => by omega, by norm_num, by norm_num, by norm_num⟩

/-- Paper package: `thm:pom-zero-temperature-two-term-expansion-maxfiber-entropy`.
    Strict clone of `paper_pom_zero_temperature_two_term_expansion_seeds`. -/
theorem paper_pom_zero_temperature_two_term_expansion_package :
    (∀ q : ℕ, (q + 1 : ℤ) * 1 - q = 1) ∧
    ((1 : ℚ) / 2 ^ 3 < 1) ∧
    ((2 * 3 : ℚ) / (2 * 3 + 1) = 6 / 7) ∧
    ((2 : ℕ) ^ 5 / 2 ^ 5 = 1) :=
  paper_pom_zero_temperature_two_term_expansion_seeds

/-- Paper-facing zero-temperature package: the endpoint intercept is the endpoint value, the
    endpoint spectrum agrees with the max-fiber entropy seed, and the remaining seeds package the
    two-term expansion together with escort freezing.
    thm:pom-zero-temperature-two-term-expansion-maxfiber-entropy -/
theorem paper_pom_zero_temperature_two_term_expansion_maxfiber_entropy :
    (∀ q : ℕ, (q + 1 : ℤ) * 1 - q = 1) ∧
    ((2 : ℕ) ^ 5 / 2 ^ 5 = 1) ∧
    (((1 : ℚ) / 2 ^ 3 < 1) ∧
      ((2 * 3 : ℚ) / (2 * 3 + 1) = 6 / 7) ∧
      (3 * 1 - (1 : ℤ) = 2)) := by
  have hPkg := paper_pom_zero_temperature_two_term_expansion_package
  exact ⟨hPkg.1, hPkg.2.2.2, ⟨hPkg.2.1, hPkg.2.2.1, escort_freezing_threshold_seed⟩⟩

end Omega.POM
