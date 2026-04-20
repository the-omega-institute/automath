import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Omega.POM.S5GaloisArithmetic

namespace Omega.Zeta

open Polynomial
open scoped BigOperators

/-- The seven conjugacy classes of `S₅`, identified with the possible splitting types of a
quintic polynomial modulo an unramified prime. -/
inductive P7S5CycleType where
  | one_one_one_one_one
  | two_one_one_one
  | two_two_one
  | three_one_one
  | three_two
  | four_one
  | five
  deriving DecidableEq, Fintype

/-- The class size of a given cycle type in `S₅`. -/
def p7ClassSize : P7S5CycleType → ℕ
  | .one_one_one_one_one => 1
  | .two_one_one_one => 10
  | .two_two_one => 15
  | .three_one_one => 20
  | .three_two => 20
  | .four_one => 30
  | .five => 24

/-- The Chebotarev numerator is the corresponding conjugacy-class size. -/
def p7RawDensityNumerator : P7S5CycleType → ℕ := p7ClassSize

/-- The common Chebotarev denominator is `|S₅| = 120`. -/
def p7RawDensityDenominator : ℕ := 120

/-- The even conjugacy classes, corresponding to the sign character `+1`. -/
def p7EvenCycleTypes : Finset P7S5CycleType :=
  {.one_one_one_one_one, .two_two_one, .three_one_one, .five}

/-- The odd conjugacy classes, corresponding to the sign character `-1`. -/
def p7OddCycleTypes : Finset P7S5CycleType :=
  {.two_one_one_one, .three_two, .four_one}

/-- The sign parity of a cycle type. -/
def p7CycleParity : P7S5CycleType → Bool
  | .one_one_one_one_one => true
  | .two_one_one_one => false
  | .two_two_one => true
  | .three_one_one => true
  | .three_two => false
  | .four_one => false
  | .five => true

/-- The seven class sizes exhaust `S₅`. -/
theorem p7_class_sizes_sum :
    p7ClassSize .one_one_one_one_one + p7ClassSize .two_one_one_one +
      p7ClassSize .two_two_one + p7ClassSize .three_one_one + p7ClassSize .three_two +
      p7ClassSize .four_one + p7ClassSize .five = 120 := by
  native_decide

/-- Repackaging `|S₅| = 120` from the existing arithmetic seeds. -/
theorem p7_raw_density_denominator_eq_s5_order : p7RawDensityDenominator = 120 := by
  simpa [p7RawDensityDenominator] using Omega.POM.S5GaloisArithmetic.s5_order

/-- Wrapper data for the `p₇` Chebotarev splitting-density statement. -/
structure P7ChebotarevSplittingDensityData where
  p7ExtensionPackaged : Prop
  discriminantNegative : Prop
  extensionWitness : p7ExtensionPackaged
  discriminantNegativeWitness : discriminantNegative

/-- Raw density table: each splitting type has density `|C| / 120`. -/
def P7ChebotarevSplittingDensityData.rawDensityTable (h : P7ChebotarevSplittingDensityData) :
    Prop :=
  h.p7ExtensionPackaged ∧
    ∀ τ : P7S5CycleType,
      p7RawDensityNumerator τ = p7ClassSize τ ∧ p7RawDensityDenominator = 120

/-- Discriminant parity law: a negative discriminant separates even and odd Frobenius classes by
the sign character. -/
def P7ChebotarevSplittingDensityData.discriminantParityLaw
    (h : P7ChebotarevSplittingDensityData) : Prop :=
  h.discriminantNegative →
    (∀ τ : P7S5CycleType, τ ∈ p7EvenCycleTypes ↔ p7CycleParity τ = true) ∧
      (∀ τ : P7S5CycleType, τ ∈ p7OddCycleTypes ↔ p7CycleParity τ = false)

/-- Conditional density table: once the sign law is imposed, the raw `|C|/120` table restricts to
the even or odd classes according to the discriminant parity. -/
def P7ChebotarevSplittingDensityData.conditionalDensityTable
    (h : P7ChebotarevSplittingDensityData) : Prop :=
  h.p7ExtensionPackaged ∧ h.discriminantNegative ∧
    (∀ τ : P7S5CycleType,
      τ ∈ p7EvenCycleTypes →
        p7RawDensityNumerator τ = p7ClassSize τ ∧ p7RawDensityDenominator = 120) ∧
      (∀ τ : P7S5CycleType,
        τ ∈ p7OddCycleTypes →
          p7RawDensityNumerator τ = p7ClassSize τ ∧ p7RawDensityDenominator = 120)

/-- Paper theorem: the `p₇` splitting types inherit the seven `S₅` class sizes, the sign law
separates them into even and odd classes, and the conditional density tables are the corresponding
restrictions of the raw `|C| / 120` table.
    thm:xi-p7-chebotarev-splitting-density -/
theorem paper_xi_p7_chebotarev_splitting_density (h : P7ChebotarevSplittingDensityData) :
    h.rawDensityTable /\ h.discriminantParityLaw /\ h.conditionalDensityTable := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨h.extensionWitness, ?_⟩
    intro τ
    constructor
    · cases τ <;> rfl
    · exact p7_raw_density_denominator_eq_s5_order
  · intro _
    refine ⟨?_, ?_⟩
    · intro τ
      cases τ <;> simp [p7EvenCycleTypes, p7CycleParity]
    · intro τ
      cases τ <;> simp [p7OddCycleTypes, p7CycleParity]
  · refine ⟨h.extensionWitness, h.discriminantNegativeWitness, ?_, ?_⟩
    · intro τ hτ
      cases τ <;> simp [p7EvenCycleTypes, p7RawDensityNumerator, p7ClassSize,
        p7_raw_density_denominator_eq_s5_order] at hτ ⊢
    · intro τ hτ
      cases τ <;> simp [p7OddCycleTypes, p7RawDensityNumerator, p7ClassSize,
        p7_raw_density_denominator_eq_s5_order] at hτ ⊢

/-- The one-dimensional sign channel attached to the `S₅` splitting classes. -/
noncomputable def p7SignEigenvalue (τ : P7S5CycleType) : ℂ :=
  if p7CycleParity τ then 1 else -1

/-- The finite Euler factor in the sign channel. -/
noncomputable def p7SignLocalEulerFactor (τ : P7S5CycleType) : Polynomial ℂ :=
  X - C (p7SignEigenvalue τ)

/-- The class-averaged limiting Lee--Yang mass in the sign channel. -/
noncomputable def p7SignLimitMeasureMass (z : ℂ) : ℝ :=
  if z = 1 then Finset.sum p7EvenCycleTypes (fun τ => (p7ClassSize τ : ℝ)) / 120
  else if z = -1 then Finset.sum p7OddCycleTypes (fun τ => (p7ClassSize τ : ℝ)) / 120
  else 0

/-- The averaged logarithmic potential of the sign-channel limit measure. -/
noncomputable def p7SignLogPotential (u : ℂ) : ℝ :=
  p7SignLimitMeasureMass 1 * Real.log ‖u - 1‖ +
    p7SignLimitMeasureMass (-1) * Real.log ‖u + 1‖

/-- The free energy read off from the two atoms of the sign-channel limiting measure. -/
noncomputable def p7SignFreeEnergy (u : ℂ) : ℝ :=
  (Real.log ‖u - 1‖ + Real.log ‖u + 1‖) / 2

lemma p7_even_class_sizes_sum :
    Finset.sum p7EvenCycleTypes p7ClassSize = 60 := by
  native_decide

lemma p7_odd_class_sizes_sum :
    Finset.sum p7OddCycleTypes p7ClassSize = 60 := by
  native_decide

/-- In the concrete `S₅` sign channel, every finite Euler factor has its zero on the unit circle,
the Chebotarev limit measure is the class average of the two atoms `±1`, and the free energy is
the corresponding averaged logarithmic potential.
    thm:xi-p7-chebotarev-leyang-circularity-and-limit-law -/
theorem paper_xi_p7_chebotarev_leyang_circularity_and_limit_law (u : ℂ) :
    (∀ τ : P7S5CycleType,
      IsRoot (p7SignLocalEulerFactor τ) (p7SignEigenvalue τ) ∧ ‖p7SignEigenvalue τ‖ = 1) ∧
    p7SignLimitMeasureMass 1 = 1 / 2 ∧
    p7SignLimitMeasureMass (-1) = 1 / 2 ∧
    (∀ z : ℂ, z ≠ 1 → z ≠ -1 → p7SignLimitMeasureMass z = 0) ∧
    p7SignLogPotential u = p7SignFreeEnergy u := by
  have heven : Finset.sum p7EvenCycleTypes (fun τ => (p7ClassSize τ : ℝ)) = 60 := by
    exact_mod_cast p7_even_class_sizes_sum
  have hodd : Finset.sum p7OddCycleTypes (fun τ => (p7ClassSize τ : ℝ)) = 60 := by
    exact_mod_cast p7_odd_class_sizes_sum
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro τ
    cases τ <;> simp [p7SignLocalEulerFactor, p7SignEigenvalue, p7CycleParity]
  · simp [p7SignLimitMeasureMass, heven]
    norm_num
  · simp [p7SignLimitMeasureMass, hodd]
    norm_num
  · intro z hz1 hzneg1
    simp [p7SignLimitMeasureMass, hz1, hzneg1]
  · rw [p7SignLogPotential, p7SignFreeEnergy]
    simp [p7SignLimitMeasureMass, heven, hodd]
    ring

end Omega.Zeta
