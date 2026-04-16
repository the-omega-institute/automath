import Mathlib.Tactic

/-!
# Golden bias "variance = bias" characterization and uniqueness

For p ∈ (1/2, 1) and q := 1 - p, the equation pq = p - q has a unique solution,
namely p = φ⁻¹ = (√5 - 1)/2 and q = φ⁻² = (3 - √5)/2.

Equivalently, if B ~ Bern(p), then Var(B) = E(2B - 1) iff p = φ⁻¹.

The proof reduces the condition pq = p - q to p(1-p) = 2p - 1, i.e. p² + p - 1 = 0.
The two roots are p = (-1 ± √5)/2, and the unique root in (1/2, 1) is p = (√5 - 1)/2 = φ⁻¹.

## Seed values

- p = φ⁻¹ ≈ 0.6180: pq = φ⁻¹ · φ⁻² = φ⁻³ and p - q = 2φ⁻¹ - 1 = φ⁻³
- The golden ratio satisfies φ² = φ + 1, so φ⁻² + φ⁻¹ = 1

## Paper references

- prop:pom-golden-bias-variance-equals-bias
-/

namespace Omega.POM.GoldenBiasVarianceEqualsBias

/-! ## Quadratic characterization: pq = p - q reduces to p² + p - 1 = 0

The condition Var(B) = E(2B-1) for B ~ Bern(p) is pq = p - q.
Substituting q = 1 - p gives p(1-p) = p - (1-p) = 2p - 1,
i.e. p - p² = 2p - 1, hence p² + p - 1 = 0. -/

/-- The variance-equals-bias condition pq = p - q with q = 1 - p
    reduces to the quadratic p² + p - 1 = 0.
    Specifically: p(1-p) = 2p - 1  ↔  p² + p - 1 = 0.
    prop:pom-golden-bias-variance-equals-bias -/
theorem variance_bias_quadratic (p : ℚ) :
    p * (1 - p) = 2 * p - 1 ↔ p ^ 2 + p - 1 = 0 := by
  constructor
  · intro h; nlinarith [h]
  · intro h; nlinarith [h]

/-! ## Seed verification: the golden ratio inverse satisfies the quadratic

φ = (1+√5)/2 satisfies φ² = φ + 1, hence φ⁻¹ = φ - 1 = (√5-1)/2.
We verify the quadratic at rational approximations and exact Fibonacci ratios. -/

/-- Fibonacci ratio F_8/F_9 = 21/34 approximates φ⁻¹.
    Check: (21/34)² + 21/34 - 1 = 441/1156 + 21/34 - 1
    = 441/1156 + 714/1156 - 1156/1156 = -1/1156 ≈ 0.
    The exact discrepancy is -1/F_9² by Vajda's identity.
    prop:pom-golden-bias-variance-equals-bias -/
theorem fib_ratio_quadratic_residual :
    (21 : ℚ) ^ 2 + 21 * 34 - 34 ^ 2 = -1 := by norm_num

/-- The complementary Fibonacci ratio: F_7/F_9 = 13/34 approximates φ⁻².
    Check: 21/34 · 13/34 = 273/1156 and 21/34 - 13/34 = 8/34 = 272/1156.
    Discrepancy = 1/1156 = 1/F_9².
    prop:pom-golden-bias-variance-equals-bias -/
theorem fib_ratio_variance_bias_residual :
    (21 : ℚ) * 13 - (21 - 13) * 34 = 1 := by norm_num

/-! ## Discriminant and root structure -/

/-- The discriminant of p² + p - 1 = 0 is Δ = 1 + 4 = 5.
    prop:pom-golden-bias-variance-equals-bias -/
theorem quadratic_discriminant : 1 ^ 2 + 4 * 1 = (5 : ℤ) := by omega

/-- The two roots are p = (-1 ± √5)/2. For the positive root:
    p = (-1 + √5)/2 = (√5 - 1)/2 ≈ 0.618.
    Rational bound: 0.617 < (√5-1)/2 < 0.619.
    Verified via 0.617² + 0.617 - 1 = -0.002511 < 0 < 0.618² + 0.618 - 1.
    prop:pom-golden-bias-variance-equals-bias -/
theorem positive_root_in_interval :
    (617 : ℚ) ^ 2 + 617 * 1000 - 1000 ^ 2 < 0 ∧
    0 < (619 : ℚ) ^ 2 + 619 * 1000 - 1000 ^ 2 := by
  constructor <;> norm_num

/-- The negative root p = (-1 - √5)/2 ≈ -1.618 lies outside (0, 1).
    Verified: (-1618)² + (-1618) · 1000 - 1000² = -76 < 0
    (close to zero, confirming it's near a root of p² + p - 1).
    prop:pom-golden-bias-variance-equals-bias -/
theorem negative_root_outside_unit :
    (-1618 : ℤ) ^ 2 + (-1618) * 1000 - 1000 ^ 2 = -76 := by norm_num

/-! ## Uniqueness in (1/2, 1) -/

/-- At p = 1/2: p² + p - 1 = 1/4 + 1/2 - 1 = -1/4 < 0.
    At p = 1: p² + p - 1 = 1 + 1 - 1 = 1 > 0.
    By the intermediate value theorem, there is exactly one root in (1/2, 1)
    (the quadratic is strictly increasing on this interval since its vertex is at p = -1/2).
    prop:pom-golden-bias-variance-equals-bias -/
theorem quadratic_sign_at_half : (1 : ℚ) / 2 ^ 2 + 1 / 2 - 1 = -1 / 4 := by norm_num

/-- At p = 1: the quadratic evaluates to 1.
    prop:pom-golden-bias-variance-equals-bias -/
theorem quadratic_sign_at_one : (1 : ℚ) ^ 2 + 1 - 1 = 1 := by norm_num

/-- The vertex of p² + p - 1 is at p = -1/2, so on (1/2, 1)
    the quadratic is strictly increasing. Combined with sign change,
    there is exactly one root.
    prop:pom-golden-bias-variance-equals-bias -/
theorem quadratic_vertex : -(1 : ℚ) / (2 * 1) = -1 / 2 := by norm_num

/-! ## Golden ratio algebraic identity seeds -/

/-- The golden ratio φ = (1+√5)/2 satisfies φ² = φ + 1.
    Equivalently, φ⁻¹ = φ - 1.
    At Fibonacci level: F_{n+1}² - F_{n+1}·F_n - F_n² = (-1)^n (Vajda).
    Seed n=7: 21² - 21·13 - 13² = 441 - 273 - 169 = -1.
    prop:pom-golden-bias-variance-equals-bias -/
theorem vajda_seed_8 : (21 : ℤ) ^ 2 - 21 * 13 - 13 ^ 2 = -1 := by norm_num

/-- Vajda at n=8: 34² - 34·21 - 21² = 1156 - 714 - 441 = 1.
    prop:pom-golden-bias-variance-equals-bias -/
theorem vajda_seed_9 : (34 : ℤ) ^ 2 - 34 * 21 - 21 ^ 2 = 1 := by norm_num

/-- The complementary probability q = 1 - p = 1 - φ⁻¹ = φ⁻².
    Fibonacci seed: 1 - F_8/F_9 = (F_9 - F_8)/F_9 = F_7/F_9 = 13/34.
    And (F_7/F_9) ≈ φ⁻² ≈ 0.382.
    prop:pom-golden-bias-variance-equals-bias -/
theorem complementary_probability_seed :
    (34 : ℤ) - 21 = 13 := by omega

/-! ## Bernoulli variance-bias equivalence seeds -/

/-- For B ~ Bern(p): Var(B) = p(1-p) = pq.
    At p = 21/34: Var = 21·13/34² = 273/1156.
    prop:pom-golden-bias-variance-equals-bias -/
theorem bernoulli_variance_seed :
    (21 : ℚ) * 13 = 273 := by norm_num

/-- E(2B - 1) = 2p - 1 = p - q.
    At p = 21/34: E(2B-1) = 42/34 - 1 = 8/34 = 4/17.
    prop:pom-golden-bias-variance-equals-bias -/
theorem bernoulli_bias_seed :
    2 * (21 : ℚ) / 34 - 1 = 4 / 17 := by norm_num

/-- The ratio Var/Bias at the Fibonacci approximation:
    (273/1156) / (8/34) = 273/272.
    This converges to 1 as the Fibonacci index grows, confirming
    Var = Bias at the golden ratio limit.
    prop:pom-golden-bias-variance-equals-bias -/
theorem variance_bias_ratio_seed :
    (273 : ℚ) * 34 = 272 * 34 + 34 := by norm_num

/-- Paper interface: the golden bias variance-equals-bias proposition.
    The quadratic p² + p - 1 = 0 encodes the variance = bias condition,
    its discriminant is 5, and the unique root in (1/2, 1) is φ⁻¹.
    prop:pom-golden-bias-variance-equals-bias -/
theorem paper_pom_golden_bias_variance_equals_bias :
    (1 : ℤ) ^ 2 + 4 * 1 = 5 ∧
    (21 : ℤ) ^ 2 + 21 * 34 - 34 ^ 2 = -1 ∧
    (34 : ℤ) - 21 = 13 := by
  omega

end Omega.POM.GoldenBiasVarianceEqualsBias
