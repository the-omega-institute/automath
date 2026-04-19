import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- The `S₅` Chebotarev density vector, ordered by cycle type
`(1^5),(2·1^3),(2^2·1),(3·1^2),(3·2),(4·1),(5)`. -/
abbrev LeyangS5DensityVector := Fin 7 → ℚ

/-- The six observed Lee-Yang coordinates coming from the `ρ₅` and `ρ₄` channels. -/
structure LeyangTwoChannelCoordinates where
  x1 : ℚ
  x2 : ℚ
  x3 : ℚ
  x4 : ℚ
  x5 : ℚ
  x6 : ℚ

/-- The five `ρ₅`-channel coordinates. -/
def rho5Coordinates (v : LeyangS5DensityVector) : ℚ × ℚ × ℚ × ℚ × ℚ :=
  (v 6 / 5, v 5 / 5, v 4 / 5, (2 * v 3 + v 4) / 5, (2 * (v 1 + v 2 + v 5)) / 5)

/-- The `ρ₄`-channel coordinate. -/
def rho4Coordinate (v : LeyangS5DensityVector) : ℚ :=
  (v 1 + 2 * v 2 + v 4 + v 5) / 4

/-- The full six-coordinate observation map. -/
def twoChannelCoordinates (v : LeyangS5DensityVector) : LeyangTwoChannelCoordinates where
  x1 := v 6 / 5
  x2 := v 5 / 5
  x3 := v 4 / 5
  x4 := (2 * v 3 + v 4) / 5
  x5 := (2 * (v 1 + v 2 + v 5)) / 5
  x6 := (v 1 + 2 * v 2 + v 4 + v 5) / 4

/-- A density vector is normalized if its coordinates sum to `1`. -/
def IsNormalizedDensity (v : LeyangS5DensityVector) : Prop :=
  v 0 + v 1 + v 2 + v 3 + v 4 + v 5 + v 6 = 1

/-- The explicit inverse formulas from the six channel coordinates. -/
def densityFive (c : LeyangTwoChannelCoordinates) : ℚ := 5 * c.x1

def densityFourOne (c : LeyangTwoChannelCoordinates) : ℚ := 5 * c.x2

def densityThreeTwo (c : LeyangTwoChannelCoordinates) : ℚ := 5 * c.x3

def densityThreeOneTwo (c : LeyangTwoChannelCoordinates) : ℚ :=
  (5 * c.x4 - densityThreeTwo c) / 2

def densityS (c : LeyangTwoChannelCoordinates) : ℚ :=
  (5 * c.x5) / 2 - densityFourOne c

def densityT (c : LeyangTwoChannelCoordinates) : ℚ :=
  4 * c.x6 - densityThreeTwo c - densityFourOne c

def densityDoubleTwoOne (c : LeyangTwoChannelCoordinates) : ℚ :=
  densityT c - densityS c

def densityTwoOneThree (c : LeyangTwoChannelCoordinates) : ℚ :=
  2 * densityS c - densityT c

def densityOneFive (c : LeyangTwoChannelCoordinates) : ℚ :=
  1 - densityTwoOneThree c - densityDoubleTwoOne c - densityThreeOneTwo c -
    densityThreeTwo c - densityFourOne c - densityFive c

/-- The reconstructed `S₅` density vector. -/
def recoveredDensityVector (c : LeyangTwoChannelCoordinates) : LeyangS5DensityVector :=
  ![densityOneFive c, densityTwoOneThree c, densityDoubleTwoOne c, densityThreeOneTwo c,
    densityThreeTwo c, densityFourOne c, densityFive c]

/-- Concrete input for the two-channel completeness theorem. -/
structure LeyangS5TwoChannelData where
  observed : LeyangTwoChannelCoordinates

namespace LeyangS5TwoChannelData

/-- The six observed coordinates uniquely determine the seven class densities. -/
def uniqueDensityRecovery (D : LeyangS5TwoChannelData) : Prop :=
  ∀ v : LeyangS5DensityVector,
    IsNormalizedDensity v → twoChannelCoordinates v = D.observed →
      v = recoveredDensityVector D.observed

/-- Each single channel loses information: `ρ₅` leaves a one-parameter ambiguity and `ρ₄` alone
cannot distinguish several nontrivial density vectors. -/
def twoChannelMinimality (_D : LeyangS5TwoChannelData) : Prop :=
  (∃ v w : LeyangS5DensityVector,
      IsNormalizedDensity v ∧ IsNormalizedDensity w ∧ rho5Coordinates v = rho5Coordinates w ∧
        v ≠ w) ∧
    ∃ v w : LeyangS5DensityVector,
      IsNormalizedDensity v ∧ IsNormalizedDensity w ∧ rho4Coordinate v = rho4Coordinate w ∧
        v ≠ w

end LeyangS5TwoChannelData

open LeyangS5TwoChannelData

def rho5WitnessLeft : LeyangS5DensityVector := fun i =>
  match i.1 with
  | 0 => 1 / 2
  | 1 => 1 / 2
  | _ => 0

def rho5WitnessRight : LeyangS5DensityVector := fun i =>
  match i.1 with
  | 0 => 1 / 2
  | 2 => 1 / 2
  | _ => 0

def rho4WitnessLeft : LeyangS5DensityVector := rho5WitnessLeft

def rho4WitnessRight : LeyangS5DensityVector := fun i =>
  match i.1 with
  | 0 => 1 / 2
  | 4 => 1 / 2
  | _ => 0

lemma rho5WitnessLeft_normalized : IsNormalizedDensity rho5WitnessLeft := by
  norm_num [IsNormalizedDensity, rho5WitnessLeft]

lemma rho5WitnessRight_normalized : IsNormalizedDensity rho5WitnessRight := by
  norm_num [IsNormalizedDensity, rho5WitnessRight]

lemma rho4WitnessLeft_normalized : IsNormalizedDensity rho4WitnessLeft := by
  exact rho5WitnessLeft_normalized

lemma rho4WitnessRight_normalized : IsNormalizedDensity rho4WitnessRight := by
  norm_num [IsNormalizedDensity, rho4WitnessRight]

lemma rho5Witness_same_channel : rho5Coordinates rho5WitnessLeft = rho5Coordinates rho5WitnessRight := by
  norm_num [rho5Coordinates, rho5WitnessLeft, rho5WitnessRight]

lemma rho5Witness_distinct : rho5WitnessLeft ≠ rho5WitnessRight := by
  intro h
  have h1 := congrArg (fun v : LeyangS5DensityVector => v 1) h
  norm_num [rho5WitnessLeft, rho5WitnessRight] at h1

lemma rho4Witness_same_channel : rho4Coordinate rho4WitnessLeft = rho4Coordinate rho4WitnessRight := by
  norm_num [rho4Coordinate, rho4WitnessLeft, rho4WitnessRight, rho5WitnessLeft]

lemma rho4Witness_distinct : rho4WitnessLeft ≠ rho4WitnessRight := by
  intro h
  have h4 := congrArg (fun v : LeyangS5DensityVector => v 4) h
  norm_num [rho4WitnessLeft, rho4WitnessRight, rho5WitnessLeft] at h4

/-- Paper-facing two-channel completeness package for the `S₅` Lee-Yang coordinates.
    thm:conclusion-leyang-s5-two-channel-minimal-completeness -/
theorem paper_conclusion_leyang_s5_two_channel_minimal_completeness
    (D : LeyangS5TwoChannelData) : D.uniqueDensityRecovery ∧ D.twoChannelMinimality := by
  refine ⟨?_, ?_⟩
  · intro v hv hcoords
    have hx1 : v 6 / 5 = D.observed.x1 := by
      simpa [twoChannelCoordinates] using congrArg LeyangTwoChannelCoordinates.x1 hcoords
    have hx2 : v 5 / 5 = D.observed.x2 := by
      simpa [twoChannelCoordinates] using congrArg LeyangTwoChannelCoordinates.x2 hcoords
    have hx3 : v 4 / 5 = D.observed.x3 := by
      simpa [twoChannelCoordinates] using congrArg LeyangTwoChannelCoordinates.x3 hcoords
    have hx4 : (2 * v 3 + v 4) / 5 = D.observed.x4 := by
      simpa [twoChannelCoordinates] using congrArg LeyangTwoChannelCoordinates.x4 hcoords
    have hx5 : (2 * (v 1 + v 2 + v 5)) / 5 = D.observed.x5 := by
      simpa [twoChannelCoordinates] using congrArg LeyangTwoChannelCoordinates.x5 hcoords
    have hx6 : (v 1 + 2 * v 2 + v 4 + v 5) / 4 = D.observed.x6 := by
      simpa [twoChannelCoordinates] using congrArg LeyangTwoChannelCoordinates.x6 hcoords
    have hv6 : v 6 = densityFive D.observed := by
      dsimp [densityFive]
      linarith
    have hv5 : v 5 = densityFourOne D.observed := by
      dsimp [densityFourOne]
      linarith
    have hv4 : v 4 = densityThreeTwo D.observed := by
      dsimp [densityThreeTwo]
      linarith
    have hv3 : v 3 = densityThreeOneTwo D.observed := by
      dsimp [densityThreeOneTwo, densityThreeTwo] at *
      linarith
    have hS : v 1 + v 2 = densityS D.observed := by
      dsimp [densityS, densityFourOne] at *
      linarith
    have hT : v 1 + 2 * v 2 = densityT D.observed := by
      dsimp [densityT, densityThreeTwo, densityFourOne] at *
      linarith
    have hv2 : v 2 = densityDoubleTwoOne D.observed := by
      dsimp [densityDoubleTwoOne]
      linarith
    have hv1 : v 1 = densityTwoOneThree D.observed := by
      dsimp [densityTwoOneThree]
      linarith
    have hsum : v 0 + v 1 + v 2 + v 3 + v 4 + v 5 + v 6 = 1 := hv
    have hv0 : v 0 = densityOneFive D.observed := by
      dsimp [densityOneFive]
      linarith
    ext i
    fin_cases i <;> simp [recoveredDensityVector, hv0, hv1, hv2, hv3, hv4, hv5, hv6]
  · refine ⟨?_, ?_⟩
    · exact ⟨rho5WitnessLeft, rho5WitnessRight, rho5WitnessLeft_normalized,
        rho5WitnessRight_normalized, rho5Witness_same_channel, rho5Witness_distinct⟩
    · exact ⟨rho4WitnessLeft, rho4WitnessRight, rho4WitnessLeft_normalized,
        rho4WitnessRight_normalized, rho4Witness_same_channel, rho4Witness_distinct⟩

end Omega.Conclusion
