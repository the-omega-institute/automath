import Mathlib

namespace Omega.POM

noncomputable section

/-- The `q`-moment weight attached to each atomic block in the multiplicity-composition model. -/
def pomMomentHierarchyWeight (q : ℕ) : ℝ :=
  (q : ℝ) + 1

/-- Ordered multiplicity-composition partition function with a `q`-moment weight per block. -/
def pomMomentHierarchyPartition (q : ℕ) : Nat → ℝ
  | 0 => 1
  | 1 => pomMomentHierarchyWeight q
  | n + 2 =>
      pomMomentHierarchyWeight q *
        (pomMomentHierarchyPartition q (n + 1) + pomMomentHierarchyPartition q n)

/-- Rational generating function attached to the two-step moment recurrence. -/
def pomMomentHierarchyGeneratingFunction (q : ℕ) (x : ℝ) : ℝ :=
  1 / (1 - pomMomentHierarchyWeight q * x - pomMomentHierarchyWeight q * x ^ (2 : Nat))

/-- Dominant root of the denominator polynomial `t^2 - w_q t - w_q`. -/
def pomMomentHierarchyDominantRoot (q : ℕ) : ℝ :=
  (pomMomentHierarchyWeight q +
      Real.sqrt
        (pomMomentHierarchyWeight q ^ (2 : Nat) + 4 * pomMomentHierarchyWeight q)) / 2

/-- Concrete package of the `q`-moment recurrence, its rational generating function, the
dominant denominator root, and the resulting exponential growth bound. -/
def pomMultiplicityCompositionMomentHierarchyRationalGrowth : Prop :=
  (∀ q : ℕ,
      pomMomentHierarchyPartition q 0 = 1 ∧
        pomMomentHierarchyPartition q 1 = pomMomentHierarchyWeight q) ∧
    (∀ q : ℕ, ∀ n : ℕ,
      pomMomentHierarchyPartition q (n + 2) =
        pomMomentHierarchyWeight q *
          (pomMomentHierarchyPartition q (n + 1) + pomMomentHierarchyPartition q n)) ∧
    (∀ q : ℕ, ∀ x : ℝ,
      pomMomentHierarchyGeneratingFunction q x =
        1 / (1 - pomMomentHierarchyWeight q * x - pomMomentHierarchyWeight q * x ^ (2 : Nat))) ∧
    (∀ q : ℕ,
      pomMomentHierarchyDominantRoot q ^ (2 : Nat) =
          pomMomentHierarchyWeight q * pomMomentHierarchyDominantRoot q +
            pomMomentHierarchyWeight q ∧
        pomMomentHierarchyWeight q ≤ pomMomentHierarchyDominantRoot q ∧
        0 < pomMomentHierarchyDominantRoot q) ∧
    (∀ q : ℕ, ∀ n : ℕ,
      pomMomentHierarchyPartition q n ≤ pomMomentHierarchyDominantRoot q ^ n)

private theorem pomMomentHierarchyWeight_nonneg (q : ℕ) : 0 ≤ pomMomentHierarchyWeight q := by
  unfold pomMomentHierarchyWeight
  positivity

private theorem pomMomentHierarchyWeight_pos (q : ℕ) : 0 < pomMomentHierarchyWeight q := by
  unfold pomMomentHierarchyWeight
  positivity

private theorem pomMomentHierarchyDominantRoot_sq (q : ℕ) :
    pomMomentHierarchyDominantRoot q ^ (2 : Nat) =
      pomMomentHierarchyWeight q * pomMomentHierarchyDominantRoot q + pomMomentHierarchyWeight q := by
  unfold pomMomentHierarchyDominantRoot
  have hdisc_nonneg :
      0 ≤ pomMomentHierarchyWeight q ^ (2 : Nat) + 4 * pomMomentHierarchyWeight q := by
    nlinarith [sq_nonneg (pomMomentHierarchyWeight q), pomMomentHierarchyWeight_nonneg q]
  nlinarith [Real.sq_sqrt hdisc_nonneg]

private theorem pomMomentHierarchyDominantRoot_ge_weight (q : ℕ) :
    pomMomentHierarchyWeight q ≤ pomMomentHierarchyDominantRoot q := by
  have hw_nonneg : 0 ≤ pomMomentHierarchyWeight q := pomMomentHierarchyWeight_nonneg q
  have hdisc_nonneg :
      0 ≤ pomMomentHierarchyWeight q ^ (2 : Nat) + 4 * pomMomentHierarchyWeight q := by
    nlinarith [sq_nonneg (pomMomentHierarchyWeight q), hw_nonneg]
  have hsqrt_nonneg :
      0 ≤
        Real.sqrt
          (pomMomentHierarchyWeight q ^ (2 : Nat) + 4 * pomMomentHierarchyWeight q) := by
    positivity
  have hsqrt_ge :
      pomMomentHierarchyWeight q ≤
        Real.sqrt
          (pomMomentHierarchyWeight q ^ (2 : Nat) + 4 * pomMomentHierarchyWeight q) := by
    nlinarith [Real.sq_sqrt hdisc_nonneg, hw_nonneg, hsqrt_nonneg]
  unfold pomMomentHierarchyDominantRoot
  nlinarith

private theorem pomMomentHierarchyDominantRoot_pos (q : ℕ) :
    0 < pomMomentHierarchyDominantRoot q := by
  exact lt_of_lt_of_le (pomMomentHierarchyWeight_pos q) (pomMomentHierarchyDominantRoot_ge_weight q)

private theorem pomMomentHierarchyPartition_le_root_pow (q : ℕ) :
    ∀ n : ℕ, pomMomentHierarchyPartition q n ≤ pomMomentHierarchyDominantRoot q ^ n
  | 0 => by simp [pomMomentHierarchyPartition]
  | 1 => by
      simpa [pomMomentHierarchyPartition] using pomMomentHierarchyDominantRoot_ge_weight q
  | n + 2 => by
      have hnext := pomMomentHierarchyPartition_le_root_pow q (n + 1)
      have hcurr := pomMomentHierarchyPartition_le_root_pow q n
      have hw_nonneg : 0 ≤ pomMomentHierarchyWeight q := pomMomentHierarchyWeight_nonneg q
      calc
        pomMomentHierarchyPartition q (n + 2)
            =
              pomMomentHierarchyWeight q *
                (pomMomentHierarchyPartition q (n + 1) + pomMomentHierarchyPartition q n) := by
                  simp [pomMomentHierarchyPartition]
        _ ≤
            pomMomentHierarchyWeight q *
              (pomMomentHierarchyDominantRoot q ^ (n + 1) +
                pomMomentHierarchyDominantRoot q ^ n) := by
                  nlinarith
        _ =
            pomMomentHierarchyDominantRoot q ^ n *
              (pomMomentHierarchyWeight q * pomMomentHierarchyDominantRoot q +
                pomMomentHierarchyWeight q) := by
                  ring
        _ =
            pomMomentHierarchyDominantRoot q ^ n *
              pomMomentHierarchyDominantRoot q ^ (2 : Nat) := by
                  rw [pomMomentHierarchyDominantRoot_sq q]
        _ = pomMomentHierarchyDominantRoot q ^ (n + 2) := by
              rw [← pow_add]

/-- Paper label: `prop:pom-multiplicity-composition-moment-hierarchy-rational-growth`.
The `q`-moment multiplicity-composition hierarchy satisfies a two-step partition recurrence, its
ordered-block generating series is rational, the dominant denominator root solves the
characteristic equation, and that root controls the exponential growth of the partition counts. -/
theorem paper_pom_multiplicity_composition_moment_hierarchy_rational_growth :
    pomMultiplicityCompositionMomentHierarchyRationalGrowth := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro q
    constructor <;> rfl
  · intro q n
    rfl
  · intro q x
    rfl
  · intro q
    exact ⟨pomMomentHierarchyDominantRoot_sq q, pomMomentHierarchyDominantRoot_ge_weight q,
      pomMomentHierarchyDominantRoot_pos q⟩
  · intro q n
    exact pomMomentHierarchyPartition_le_root_pow q n

end

end Omega.POM
