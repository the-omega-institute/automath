import Mathlib.Tactic

/-!
# Typeclass diagonal coupling scalarization seeds

The marginal constraint P_X = P_Y = w with diagonal coupling parameter κ > -1
leads to the quadratic equation
  κ u² + A u - w = 0
whose positive root is
  u(A, κ) = (-A + √(A² + 4κw)) / (2κ)     when κ ≠ 0
  u(A, κ) = w / A                            when κ = 0

The self-consistency condition A = Σ_x u_x(A, κ) determines a unique A(κ) > 0.

## Seed values

At integer level, the quadratic κ u² + A u - w = 0 can be verified:
- κ=1, A=1, w=2: u² + u - 2 = 0 has root u=1 (since 1+1-2=0)
- κ=2, A=3, w=5: 2u² + 3u - 5 = 0 has root u=1 (since 2+3-5=0)
- κ=0 case: u = w/A is linear

The discriminant Δ = A² + 4κw determines root existence.

## Paper references

- thm:pom-typeclass-diagonal-coupling-scalarization
-/

namespace Omega.POM.TypeclassDiagonalCouplingSeeds

/-! ## Quadratic constraint: κ u² + A u - w = 0

The marginal constraint for diagonal coupling reduces to a quadratic in u. -/

/-- Quadratic constraint function: κ u² + A u - w.
    thm:pom-typeclass-diagonal-coupling-scalarization -/
def quadConstraint (kappa A w u : ℤ) : ℤ := kappa * u ^ 2 + A * u - w

/-- Quadratic root seed: κ=1, A=1, w=2, u=1 satisfies the constraint.
    thm:pom-typeclass-diagonal-coupling-scalarization -/
theorem quadConstraint_seed_1_1_2 : quadConstraint 1 1 2 1 = 0 := by
  simp [quadConstraint]

/-- Quadratic root seed: κ=2, A=3, w=5, u=1 satisfies the constraint.
    thm:pom-typeclass-diagonal-coupling-scalarization -/
theorem quadConstraint_seed_2_3_5 : quadConstraint 2 3 5 1 = 0 := by
  simp [quadConstraint]

/-- Quadratic root seed: κ=1, A=5, w=6, u=1 satisfies the constraint.
    1 + 5 - 6 = 0.
    thm:pom-typeclass-diagonal-coupling-scalarization -/
theorem quadConstraint_seed_1_5_6 : quadConstraint 1 5 6 1 = 0 := by
  simp [quadConstraint]

/-- Quadratic root seed: κ=1, A=-3, w=4, u=1 satisfies the constraint.
    1 - 3 - 4 = -6 ≠ 0, so try u=4: 16-12-4=0. Actually κ=1,A=0,w=4,u=2: 4+0-4=0.
    thm:pom-typeclass-diagonal-coupling-scalarization -/
theorem quadConstraint_seed_1_0_4 : quadConstraint 1 0 4 2 = 0 := by
  simp [quadConstraint]

/-- Quadratic root seed: κ=3, A=1, w=4, u=1 satisfies 3+1-4=0.
    thm:pom-typeclass-diagonal-coupling-scalarization -/
theorem quadConstraint_seed_3_1_4 : quadConstraint 3 1 4 1 = 0 := by
  simp [quadConstraint]

/-! ## Discriminant: Δ = A² + 4κw

The discriminant determines whether the quadratic has real roots.
For κ > 0 and w > 0, we always have Δ > A² > 0, ensuring a positive root. -/

/-- Discriminant function for the diagonal coupling quadratic.
    thm:pom-typeclass-diagonal-coupling-scalarization -/
def discriminant (kappa A w : ℤ) : ℤ := A ^ 2 + 4 * kappa * w

/-- Discriminant seed: κ=1, A=1, w=2 gives Δ = 1 + 8 = 9.
    thm:pom-typeclass-diagonal-coupling-scalarization -/
theorem discriminant_seed_1_1_2 : discriminant 1 1 2 = 9 := by
  simp [discriminant]

/-- Discriminant seed: κ=2, A=3, w=5 gives Δ = 9 + 40 = 49.
    thm:pom-typeclass-diagonal-coupling-scalarization -/
theorem discriminant_seed_2_3_5 : discriminant 2 3 5 = 49 := by
  simp [discriminant]

/-- Discriminant seed: κ=1, A=0, w=4 gives Δ = 0 + 16 = 16.
    thm:pom-typeclass-diagonal-coupling-scalarization -/
theorem discriminant_seed_1_0_4 : discriminant 1 0 4 = 16 := by
  simp [discriminant]

/-- Discriminant positivity: for κ > 0 and w > 0, Δ > 0.
    thm:pom-typeclass-diagonal-coupling-scalarization -/
theorem discriminant_pos_of_pos (kappa A w : ℤ) (hk : 0 < kappa) (hw : 0 < w) :
    0 < discriminant kappa A w := by
  simp [discriminant]; nlinarith [sq_nonneg A]

/-! ## Linear case: κ = 0 gives u = w / A

When the diagonal excess vanishes, the constraint becomes linear: Au = w. -/

/-- Linear constraint: when κ=0, the quadratic reduces to Au - w.
    thm:pom-typeclass-diagonal-coupling-scalarization -/
theorem quadConstraint_linear (A w u : ℤ) :
    quadConstraint 0 A w u = A * u - w := by
  simp [quadConstraint]

/-- Linear root verification: κ=0, A=3, w=6, u=2 satisfies 3·2-6=0.
    thm:pom-typeclass-diagonal-coupling-scalarization -/
theorem linear_root_seed : quadConstraint 0 3 6 2 = 0 := by
  simp [quadConstraint]

/-! ## Self-consistency: A = Σ u_x(A, κ)

For a system with n identical weights w(x) = 1/n, the self-consistency
condition becomes A = n · u(A, κ), i.e. κ(A/n)² + A(A/n) - 1/n = 0.
At integer level with n copies of weight w, the total Σ u_x = n·u
must equal A. -/

/-- Self-consistency seed: n copies with equal u satisfy n·u = A.
    If κ=1, u=1, w=1+A (from u²+Au-w=0 → w=1+A), and n·1 = A → A=n.
    For n=2: w=3, quadConstraint 1 2 3 1 = 1+2-3 = 0.
    thm:pom-typeclass-diagonal-coupling-scalarization -/
theorem selfConsistency_n2 : quadConstraint 1 2 3 1 = 0 ∧ 2 * 1 = 2 := by
  constructor
  · simp [quadConstraint]
  · ring

/-- Self-consistency seed: n=3, κ=1, A=3, u=1, w=4.
    quadConstraint 1 3 4 1 = 1+3-4 = 0, and 3·1 = 3.
    thm:pom-typeclass-diagonal-coupling-scalarization -/
theorem selfConsistency_n3 : quadConstraint 1 3 4 1 = 0 ∧ 3 * 1 = 3 := by
  constructor
  · simp [quadConstraint]
  · ring

/-- Self-consistency seed: n=5, κ=1, A=5, u=1, w=6.
    quadConstraint 1 5 6 1 = 1+5-6 = 0, and 5·1 = 5.
    thm:pom-typeclass-diagonal-coupling-scalarization -/
theorem selfConsistency_n5 : quadConstraint 1 5 6 1 = 0 ∧ 5 * 1 = 5 := by
  constructor
  · simp [quadConstraint]
  · ring

/-- Paper wrapper: Typeclass diagonal coupling scalarization seeds.
    Quadratic roots, discriminant values, linear case, and self-consistency.
    thm:pom-typeclass-diagonal-coupling-scalarization -/
theorem paper_pom_typeclass_diagonal_coupling_seeds :
    quadConstraint 1 1 2 1 = 0 ∧ quadConstraint 2 3 5 1 = 0
    ∧ discriminant 1 1 2 = 9 ∧ discriminant 2 3 5 = 49
    ∧ quadConstraint 0 3 6 2 = 0
    ∧ (quadConstraint 1 2 3 1 = 0 ∧ 2 * 1 = 2) := by
  exact ⟨quadConstraint_seed_1_1_2, quadConstraint_seed_2_3_5,
    discriminant_seed_1_1_2, discriminant_seed_2_3_5,
    linear_root_seed, selfConsistency_n2⟩

/-- Package wrapper for the typeclass diagonal coupling scalarization seeds.
    thm:pom-typeclass-diagonal-coupling-scalarization -/
theorem paper_pom_typeclass_diagonal_coupling_package :
    quadConstraint 1 1 2 1 = 0 ∧ quadConstraint 2 3 5 1 = 0
    ∧ discriminant 1 1 2 = 9 ∧ discriminant 2 3 5 = 49
    ∧ quadConstraint 0 3 6 2 = 0
    ∧ (quadConstraint 1 2 3 1 = 0 ∧ 2 * 1 = 2) :=
  paper_pom_typeclass_diagonal_coupling_seeds

end Omega.POM.TypeclassDiagonalCouplingSeeds
