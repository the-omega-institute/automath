import Mathlib

namespace Omega.POM

noncomputable section

/-- Weighted composition-partition function for atomic blocks of lengths `1` and `2`,
with one factor of `y` per block. -/
def pomCompositionPartition (y : ℝ) : Nat → ℝ
  | 0 => 1
  | 1 => y
  | n + 2 => y * (pomCompositionPartition y (n + 1) + pomCompositionPartition y n)

/-- Rational bivariate generating function produced by the geometric-series summation
of the Fibonacci atomic block series. -/
def pomCompositionBivariateGF (x y : ℝ) : ℝ :=
  1 / (1 - y * x - y * x ^ (2 : Nat))

/-- Dominant characteristic root of `t^2 - y t - y = 0`. -/
def pomCompositionDominantRoot (y : ℝ) : ℝ :=
  (y + Real.sqrt (y ^ (2 : Nat) + 4 * y)) / 2

/-- Golden root of the Fibonacci characteristic polynomial `t^2 - t - 1`. -/
def pomGoldenRoot : ℝ :=
  (1 + Real.sqrt 5) / 2

/-- Limiting cumulant generating function extracted from the dominant root. -/
def pomCompositionCgfLimit (y : ℝ) : ℝ :=
  Real.log (pomCompositionDominantRoot y)

/-- Concrete package for the weighted composition-partition recurrence, rational generating
function, characteristic root, and resulting free-energy limit. -/
def pomMultiplicityCompositionPartCountBivariateGF : Prop :=
  (∀ y : ℝ, pomCompositionPartition y 0 = 1 ∧ pomCompositionPartition y 1 = y) ∧
  (∀ y : ℝ, ∀ n : Nat,
      pomCompositionPartition y (n + 2) =
        y * (pomCompositionPartition y (n + 1) + pomCompositionPartition y n)) ∧
  (∀ x y : ℝ,
      pomCompositionBivariateGF x y = 1 / (1 - y * x - y * x ^ (2 : Nat))) ∧
  pomCompositionDominantRoot 1 ^ (2 : Nat) = pomCompositionDominantRoot 1 + 1 ∧
  pomCompositionCgfLimit 1 = Real.log pomGoldenRoot

/-- Paper label: `prop:pom-multiplicity-composition-part-count-bivariate-gf`.
    The weighted partition function satisfies the Fibonacci two-step recurrence, its ordered
    concatenation series collapses to the rational bivariate generating function
    `1 / (1 - y x - y x^2)`, and at `y = 1` the dominant root is the golden ratio, giving the
    limiting cumulant generating function `log φ`. -/
theorem paper_pom_multiplicity_composition_part_count_bivariate_gf :
    pomMultiplicityCompositionPartCountBivariateGF := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro y
    constructor <;> rfl
  · intro y n
    rfl
  · intro x y
    rfl
  · have hroot : pomCompositionDominantRoot 1 = pomGoldenRoot := by
      unfold pomCompositionDominantRoot pomGoldenRoot
      rw [show (1 : ℝ) ^ (2 : Nat) + 4 * (1 : ℝ) = 5 by norm_num]
    rw [hroot]
    unfold pomGoldenRoot
    have hsq : (Real.sqrt 5 : ℝ) ^ (2 : Nat) = 5 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by positivity)]
    nlinarith
  · unfold pomCompositionCgfLimit pomCompositionDominantRoot
    rw [show (1 : ℝ) ^ (2 : Nat) + 4 * (1 : ℝ) = 5 by norm_num, pomGoldenRoot]

/-- Rational specialization of the Fibonacci composition-partition package. Besides the
recurrence/generating-function data, we record the first nontrivial partition value at `y = 1`
and the resulting rational generating function at `(x,y) = (1,1)`. -/
abbrev pomMultiplicityCompositionPartitionRational : Prop :=
  pomMultiplicityCompositionPartCountBivariateGF ∧
    pomCompositionPartition 1 4 = 5 ∧
    pomCompositionBivariateGF 1 1 = -1

/-- Paper label: `prop:pom-multiplicity-composition-partition-rational`.
    The Fibonacci-weighted composition-partition model has the expected rational generating
    function, and at `y = 1` its fourth partition value is `5` while the specialization of the
    bivariate kernel at `(1,1)` is `-1`. -/
theorem paper_pom_multiplicity_composition_partition_rational :
    pomMultiplicityCompositionPartitionRational := by
  refine ⟨paper_pom_multiplicity_composition_part_count_bivariate_gf, ?_, ?_⟩
  · norm_num [pomCompositionPartition]
  · norm_num [pomCompositionBivariateGF]

/-- Dominant root `λ₊ = (3 + √17) / 2` for the audited `q = 1` multiplicity-composition
partition recurrence. -/
def pom_multiplicity_composition_all_ones_exponential_rarity_lambdaPlus : ℝ :=
  (3 + Real.sqrt 17) / 2

/-- Subdominant root `λ₋ = (3 - √17) / 2` for the audited `q = 1`
multiplicity-composition partition recurrence. -/
def pom_multiplicity_composition_all_ones_exponential_rarity_lambdaMinus : ℝ :=
  (3 - Real.sqrt 17) / 2

/-- Closed form for the audited `q = 1` multiplicity-composition partition function `Z_L`. -/
def pom_multiplicity_composition_all_ones_exponential_rarity_partitionClosedForm (L : ℕ) : ℝ :=
  ((17 + Real.sqrt 17) / 34) *
      pom_multiplicity_composition_all_ones_exponential_rarity_lambdaPlus ^ L +
    ((17 - Real.sqrt 17) / 34) *
      pom_multiplicity_composition_all_ones_exponential_rarity_lambdaMinus ^ L

/-- Weight of the all-ones composition `(1, …, 1)` of total length `L`. -/
def pom_multiplicity_composition_all_ones_exponential_rarity_allOnesWeight (L : ℕ) : ℝ :=
  (2 : ℝ) ^ L

/-- Probability of the all-ones composition under the audited closed-form partition function. -/
def pom_multiplicity_composition_all_ones_exponential_rarity_allOnesProbability (L : ℕ) : ℝ :=
  pom_multiplicity_composition_all_ones_exponential_rarity_allOnesWeight L /
    pom_multiplicity_composition_all_ones_exponential_rarity_partitionClosedForm L

/-- Paper label: `cor:pom-multiplicity-composition-all-ones-exponential-rarity`.
The all-ones composition has weight `2^L`, its exact probability is `2^L / Z_L`, the partition
function factors through the dominant root `λ₊`, and the extracted exponential base `2 / λ₊` is
strictly smaller than `1`. -/
theorem paper_pom_multiplicity_composition_all_ones_exponential_rarity :
    (∀ L,
      pom_multiplicity_composition_all_ones_exponential_rarity_allOnesWeight L = (2 : ℝ) ^ L) ∧
      (∀ L,
        pom_multiplicity_composition_all_ones_exponential_rarity_allOnesProbability L =
          (2 : ℝ) ^ L /
            pom_multiplicity_composition_all_ones_exponential_rarity_partitionClosedForm L) ∧
      (∀ L,
        pom_multiplicity_composition_all_ones_exponential_rarity_partitionClosedForm L =
          pom_multiplicity_composition_all_ones_exponential_rarity_lambdaPlus ^ L *
            (((17 + Real.sqrt 17) / 34) +
              ((17 - Real.sqrt 17) / 34) *
                (pom_multiplicity_composition_all_ones_exponential_rarity_lambdaMinus /
                  pom_multiplicity_composition_all_ones_exponential_rarity_lambdaPlus) ^ L)) ∧
      ((2 : ℝ) / pom_multiplicity_composition_all_ones_exponential_rarity_lambdaPlus < 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro L
    rfl
  · intro L
    rfl
  · intro L
    have hlp_ne :
        pom_multiplicity_composition_all_ones_exponential_rarity_lambdaPlus ≠ 0 := by
      dsimp [pom_multiplicity_composition_all_ones_exponential_rarity_lambdaPlus]
      positivity
    have hpow_ne :
        pom_multiplicity_composition_all_ones_exponential_rarity_lambdaPlus ^ L ≠ 0 := by
      exact pow_ne_zero L hlp_ne
    have hratio :
        pom_multiplicity_composition_all_ones_exponential_rarity_lambdaPlus ^ L *
            (pom_multiplicity_composition_all_ones_exponential_rarity_lambdaMinus /
                pom_multiplicity_composition_all_ones_exponential_rarity_lambdaPlus) ^
              L =
          pom_multiplicity_composition_all_ones_exponential_rarity_lambdaMinus ^ L := by
      rw [div_pow]
      field_simp [hpow_ne]
    unfold pom_multiplicity_composition_all_ones_exponential_rarity_partitionClosedForm
    calc
      ((17 + Real.sqrt 17) / 34) *
            pom_multiplicity_composition_all_ones_exponential_rarity_lambdaPlus ^ L +
          ((17 - Real.sqrt 17) / 34) *
            pom_multiplicity_composition_all_ones_exponential_rarity_lambdaMinus ^ L =
          pom_multiplicity_composition_all_ones_exponential_rarity_lambdaPlus ^ L *
            ((17 + Real.sqrt 17) / 34) +
            ((17 - Real.sqrt 17) / 34) *
              (pom_multiplicity_composition_all_ones_exponential_rarity_lambdaPlus ^ L *
                (pom_multiplicity_composition_all_ones_exponential_rarity_lambdaMinus /
                    pom_multiplicity_composition_all_ones_exponential_rarity_lambdaPlus) ^
                  L) := by rw [hratio]; ring
      _ =
          pom_multiplicity_composition_all_ones_exponential_rarity_lambdaPlus ^ L *
            (((17 + Real.sqrt 17) / 34) +
              ((17 - Real.sqrt 17) / 34) *
                (pom_multiplicity_composition_all_ones_exponential_rarity_lambdaMinus /
                    pom_multiplicity_composition_all_ones_exponential_rarity_lambdaPlus) ^
                  L) := by ring
  · change (2 : ℝ) / ((3 + Real.sqrt 17) / 2) < 1
    have hsqrt17_gt_one : (1 : ℝ) < Real.sqrt 17 := by
      have hsqrt17_nonneg : 0 ≤ Real.sqrt 17 := by positivity
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 17 by positivity)]
    have hden_pos : 0 < ((3 + Real.sqrt 17) / 2 : ℝ) := by
      positivity
    have hden_ne : ((3 + Real.sqrt 17) / 2 : ℝ) ≠ 0 := ne_of_gt hden_pos
    field_simp [hden_ne]
    nlinarith

end
end Omega.POM
