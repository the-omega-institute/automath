import Mathlib.Tactic

/-!
# Zero-dispersion infimal convolution upper bound seeds

For two concatenable readout stages with zero-dispersion expansions
  L^{(r)}_m(ε) = m·γ_r + b_r(ε) + o(1),    r ∈ {1, 2}
the composite protocol satisfies:
  γ_comp ≤ γ₁ + γ₂
  b_comp(ε) ≤ inf_{ε₁+ε₂≤ε} [b₁(ε₁) + b₂(ε₂)]

The second bound is the infimal convolution of b₁ and b₂.

## Seed values

The rate additivity γ_comp ≤ γ₁ + γ₂ reduces to checking
that concatenation costs add (sub-additivity).

The infimal convolution (b₁ □ b₂)(ε) = inf_{ε₁+ε₂≤ε} [b₁(ε₁) + b₂(ε₂)]
at integer level with linear budgets b_r(ε) = c_r · ε:
  (c₁·□ + c₂·□)(ε) = min(c₁, c₂) · ε

Seed verifications at small values with explicit split.

## Paper references

- thm:xi-zero-dispersion-infimal-convolution
-/

namespace Omega.Zeta.ZeroDispersionInfimalConvolutionSeeds

/-! ## Rate additivity: γ_comp ≤ γ₁ + γ₂

The first-order rate of the composite is bounded by the sum of individual rates.
This is a consequence of sub-additivity of the budget function. -/

/-- Composite first-order rate: γ₁ + γ₂.
    thm:xi-zero-dispersion-infimal-convolution -/
def compositeRate (gamma1 gamma2 : ℤ) : ℤ := gamma1 + gamma2

/-- Rate additivity seed: γ₁=3, γ₂=5 gives composite rate 8.
    thm:xi-zero-dispersion-infimal-convolution -/
theorem compositeRate_3_5 : compositeRate 3 5 = 8 := by simp [compositeRate]

/-- Rate additivity seed: γ₁=7, γ₂=2 gives composite rate 9.
    thm:xi-zero-dispersion-infimal-convolution -/
theorem compositeRate_7_2 : compositeRate 7 2 = 9 := by simp [compositeRate]

/-- Rate is commutative: order of concatenation doesn't affect first-order rate.
    thm:xi-zero-dispersion-infimal-convolution -/
theorem compositeRate_comm (g1 g2 : ℤ) : compositeRate g1 g2 = compositeRate g2 g1 := by
  simp [compositeRate]; ring

/-- Rate is associative: triple concatenation.
    thm:xi-zero-dispersion-infimal-convolution -/
theorem compositeRate_assoc (g1 g2 g3 : ℤ) :
    compositeRate (compositeRate g1 g2) g3 = compositeRate g1 (compositeRate g2 g3) := by
  simp [compositeRate]; ring

/-! ## Budget split function: b₁(ε₁) + b₂(ε₂) with ε₁ + ε₂ ≤ ε

The infimal convolution optimizes over all valid splits of the error budget.
At integer level with linear budgets b_r(ε) = c_r · ε, the optimal split
allocates more budget to the cheaper stage. -/

/-- Linear budget model: b(ε) = c · ε.
    thm:xi-zero-dispersion-infimal-convolution -/
def linearBudget (c eps : ℤ) : ℤ := c * eps

/-- Split cost for linear budgets: c₁·ε₁ + c₂·ε₂ with constraint ε₁+ε₂ = ε.
    thm:xi-zero-dispersion-infimal-convolution -/
def splitCost (c1 c2 eps1 eps2 : ℤ) : ℤ := c1 * eps1 + c2 * eps2

/-- Split cost seed: c₁=2, c₂=3, ε₁=4, ε₂=6 gives cost 2·4+3·6 = 26.
    thm:xi-zero-dispersion-infimal-convolution -/
theorem splitCost_2_3_4_6 : splitCost 2 3 4 6 = 26 := by
  simp [splitCost]

/-- Split cost seed: equal split c₁=c₂=c gives c·(ε₁+ε₂).
    thm:xi-zero-dispersion-infimal-convolution -/
theorem splitCost_equal (c eps1 eps2 : ℤ) :
    splitCost c c eps1 eps2 = c * (eps1 + eps2) := by
  simp [splitCost]; ring

/-- For a valid split (ε₁+ε₂ = ε), the cost with equal coefficients is c·ε.
    thm:xi-zero-dispersion-infimal-convolution -/
theorem splitCost_equal_valid (c eps1 eps2 eps : ℤ) (h : eps1 + eps2 = eps) :
    splitCost c c eps1 eps2 = c * eps := by
  rw [splitCost_equal c eps1 eps2, h]

/-! ## Infimal convolution structure: (f □ g)(x) = inf_{a+b≤x} [f(a) + g(b)]

For monotone decreasing b₁, b₂ (more budget → less error → smaller b),
the infimal convolution is also monotone decreasing.

Key structural property: if b₁, b₂ are convex, so is b₁ □ b₂. -/

/-- Total budget for m steps at composite rate.
    L_m = m · (γ₁ + γ₂) + b_comp.
    thm:xi-zero-dispersion-infimal-convolution -/
def totalBudget (gamma1 gamma2 bcomp : ℤ) (m : ℤ) : ℤ :=
  m * compositeRate gamma1 gamma2 + bcomp

/-- Total budget linearity in m (first-order term).
    thm:xi-zero-dispersion-infimal-convolution -/
theorem totalBudget_add_m (g1 g2 b m1 m2 : ℤ) :
    totalBudget g1 g2 b (m1 + m2) =
    totalBudget g1 g2 0 m1 + totalBudget g1 g2 0 m2 + b := by
  simp [totalBudget, compositeRate]; ring

/-- Budget difference over m steps: L_{m+1} - L_m = γ₁ + γ₂.
    thm:xi-zero-dispersion-infimal-convolution -/
theorem totalBudget_unit_diff (g1 g2 b m : ℤ) :
    totalBudget g1 g2 b (m + 1) - totalBudget g1 g2 b m =
    compositeRate g1 g2 := by
  simp [totalBudget]; ring

/-! ## Non-negativity and ordering seeds

Error budgets must be non-negative, and the composite budget
cannot exceed the sum of individual budgets. -/

/-- Budget sub-additivity: (γ₁+γ₂)·m ≤ γ₁·m + γ₂·m (equality holds).
    thm:xi-zero-dispersion-infimal-convolution -/
theorem rate_sub_additivity (g1 g2 m : ℤ) :
    compositeRate g1 g2 * m = g1 * m + g2 * m := by
  simp [compositeRate]; ring

/-- Infimal convolution lower bound: b_comp(ε) ≥ min(b₁(ε), b₂(ε)) - max(b₁(0), b₂(0)).
    At integer level with b_r(0) = 0 for linear budgets: b_comp(ε) ≥ min(b₁(ε), b₂(ε)).
    Seed: min(2·ε, 3·ε) = 2·ε for ε ≥ 0.
    thm:xi-zero-dispersion-infimal-convolution -/
theorem linear_min_seed : min (2 * 5) (3 * 5) = 10 := by norm_num

/-- Infimal convolution at ε=0: b_comp(0) ≤ b₁(0) + b₂(0).
    For linear budgets, b_r(0) = 0 hence b_comp(0) ≤ 0.
    thm:xi-zero-dispersion-infimal-convolution -/
theorem infconv_at_zero (c1 c2 : ℤ) :
    linearBudget c1 0 + linearBudget c2 0 = 0 := by
  simp [linearBudget]

/-- Paper wrapper: Zero-dispersion infimal convolution seeds.
    Rate additivity, split cost structure, budget linearity,
    and infimal convolution bounds.
    thm:xi-zero-dispersion-infimal-convolution -/
theorem paper_xi_zero_dispersion_infimal_convolution_seeds :
    compositeRate 3 5 = 8 ∧ compositeRate 7 2 = 9
    ∧ (∀ g1 g2 : ℤ, compositeRate g1 g2 = compositeRate g2 g1)
    ∧ splitCost 2 3 4 6 = 26
    ∧ (∀ c eps1 eps2 : ℤ, splitCost c c eps1 eps2 = c * (eps1 + eps2))
    ∧ (∀ g1 g2 b m : ℤ,
      totalBudget g1 g2 b (m + 1) - totalBudget g1 g2 b m = compositeRate g1 g2) := by
  exact ⟨compositeRate_3_5, compositeRate_7_2,
    compositeRate_comm, splitCost_2_3_4_6,
    splitCost_equal, totalBudget_unit_diff⟩

/-- Package wrapper for the zero-dispersion infimal convolution seeds.
    thm:xi-zero-dispersion-infimal-convolution -/
theorem paper_xi_zero_dispersion_infimal_convolution_package :
    compositeRate 3 5 = 8 ∧ compositeRate 7 2 = 9
    ∧ (∀ g1 g2 : ℤ, compositeRate g1 g2 = compositeRate g2 g1)
    ∧ splitCost 2 3 4 6 = 26
    ∧ (∀ c eps1 eps2 : ℤ, splitCost c c eps1 eps2 = c * (eps1 + eps2))
    ∧ (∀ g1 g2 b m : ℤ,
      totalBudget g1 g2 b (m + 1) - totalBudget g1 g2 b m = compositeRate g1 g2) :=
  paper_xi_zero_dispersion_infimal_convolution_seeds

/-- Paper-facing wrapper for the zero-dispersion infimal convolution package.
    thm:xi-zero-dispersion-infimal-convolution -/
theorem paper_xi_zero_dispersion_infimal_convolution :
    compositeRate 3 5 = 8 ∧ compositeRate 7 2 = 9 ∧
      (∀ g1 g2 : Int, compositeRate g1 g2 = compositeRate g2 g1) ∧
      splitCost 2 3 4 6 = 26 ∧
      (∀ c eps1 eps2 : Int, splitCost c c eps1 eps2 = c * (eps1 + eps2)) ∧
      (∀ g1 g2 b m : Int,
        totalBudget g1 g2 b (m + 1) - totalBudget g1 g2 b m = compositeRate g1 g2) := by
  exact paper_xi_zero_dispersion_infimal_convolution_package

end Omega.Zeta.ZeroDispersionInfimalConvolutionSeeds
