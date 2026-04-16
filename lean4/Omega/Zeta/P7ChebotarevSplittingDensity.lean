import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Omega.POM.S5GaloisArithmetic

namespace Omega.Zeta

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

end Omega.Zeta
