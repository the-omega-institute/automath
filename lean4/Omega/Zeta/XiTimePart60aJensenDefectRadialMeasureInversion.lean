import Mathlib.Tactic

namespace Omega.Zeta

/-- One finite atom of the radial zero ledger on the integer log-radius line. -/
structure xi_time_part60a_jensen_defect_radial_measure_inversion_atom where
  radius : ℤ
  weight : ℕ

/-- Concrete finite data for Jensen-defect radial measure inversion. -/
structure xi_time_part60a_jensen_defect_radial_measure_inversion_data where
  atoms : List xi_time_part60a_jensen_defect_radial_measure_inversion_atom

/-- The one-sided hinge `(t - c)_+` on the integer log-radius line. -/
def xi_time_part60a_jensen_defect_radial_measure_inversion_hinge (c t : ℤ) : ℤ :=
  if c ≤ t then t - c else 0

/-- The Jensen potential contribution of one weighted atom. -/
def xi_time_part60a_jensen_defect_radial_measure_inversion_atomPotential
    (a : xi_time_part60a_jensen_defect_radial_measure_inversion_atom) (t : ℤ) : ℤ :=
  (a.weight : ℤ) * xi_time_part60a_jensen_defect_radial_measure_inversion_hinge a.radius t

/-- Finite Jensen potential as a sum of weighted hinge terms. -/
def xi_time_part60a_jensen_defect_radial_measure_inversion_potentialOf :
    List xi_time_part60a_jensen_defect_radial_measure_inversion_atom → ℤ → ℤ
  | [], _ => 0
  | a :: atoms, t =>
      xi_time_part60a_jensen_defect_radial_measure_inversion_atomPotential a t +
        xi_time_part60a_jensen_defect_radial_measure_inversion_potentialOf atoms t

/-- Cumulative mass at or below a log-radius. -/
def xi_time_part60a_jensen_defect_radial_measure_inversion_cumulativeOf :
    List xi_time_part60a_jensen_defect_radial_measure_inversion_atom → ℤ → ℤ
  | [], _ => 0
  | a :: atoms, t =>
      (if a.radius ≤ t then (a.weight : ℤ) else 0) +
        xi_time_part60a_jensen_defect_radial_measure_inversion_cumulativeOf atoms t

/-- Atomic mass exactly at a log-radius. -/
def xi_time_part60a_jensen_defect_radial_measure_inversion_measureOf :
    List xi_time_part60a_jensen_defect_radial_measure_inversion_atom → ℤ → ℤ
  | [], _ => 0
  | a :: atoms, t =>
      (if a.radius = t then (a.weight : ℤ) else 0) +
        xi_time_part60a_jensen_defect_radial_measure_inversion_measureOf atoms t

namespace xi_time_part60a_jensen_defect_radial_measure_inversion_data

/-- Jensen potential induced by the finite radial ledger. -/
def jensenPotential
    (D : xi_time_part60a_jensen_defect_radial_measure_inversion_data) (t : ℤ) : ℤ :=
  xi_time_part60a_jensen_defect_radial_measure_inversion_potentialOf D.atoms t

/-- First forward difference of the Jensen potential. -/
def forwardSlope
    (D : xi_time_part60a_jensen_defect_radial_measure_inversion_data) (t : ℤ) : ℤ :=
  D.jensenPotential (t + 1) - D.jensenPotential t

/-- Second centered discrete distributional derivative of the Jensen potential. -/
def secondDifference
    (D : xi_time_part60a_jensen_defect_radial_measure_inversion_data) (t : ℤ) : ℤ :=
  D.jensenPotential (t + 1) - 2 * D.jensenPotential t + D.jensenPotential (t - 1)

/-- Radial ledger mass exactly at `t`. -/
def radialMeasure
    (D : xi_time_part60a_jensen_defect_radial_measure_inversion_data) (t : ℤ) : ℤ :=
  xi_time_part60a_jensen_defect_radial_measure_inversion_measureOf D.atoms t

/-- Cumulative zero count at or below `t`. -/
def cumulativeZeroCount
    (D : xi_time_part60a_jensen_defect_radial_measure_inversion_data) (t : ℤ) : ℤ :=
  xi_time_part60a_jensen_defect_radial_measure_inversion_cumulativeOf D.atoms t

/-- The potential is represented as the finite sum of weighted hinge terms. -/
def jensenPotentialRepresentation
    (D : xi_time_part60a_jensen_defect_radial_measure_inversion_data) : Prop :=
  ∀ t : ℤ,
    D.jensenPotential t =
      xi_time_part60a_jensen_defect_radial_measure_inversion_potentialOf D.atoms t

/-- Convexity is nonnegative distributional curvature; piecewise affinity is constant slope
between the finite ledger atoms, encoded by the cumulative-count slope formula. -/
def convexPiecewiseAffine
    (D : xi_time_part60a_jensen_defect_radial_measure_inversion_data) : Prop :=
  (∀ t : ℤ, 0 ≤ D.secondDifference t) ∧
    (∀ t : ℤ, D.forwardSlope t = D.cumulativeZeroCount t)

/-- First derivative counts the atoms whose radii have already been crossed. -/
def derivativeCountsZeros
    (D : xi_time_part60a_jensen_defect_radial_measure_inversion_data) : Prop :=
  ∀ t : ℤ, D.forwardSlope t = D.cumulativeZeroCount t

/-- The second distributional derivative recovers the original radial atomic measure. -/
def secondDistributionDerivativeRecoversMeasure
    (D : xi_time_part60a_jensen_defect_radial_measure_inversion_data) : Prop :=
  ∀ t : ℤ, D.secondDifference t = D.radialMeasure t

end xi_time_part60a_jensen_defect_radial_measure_inversion_data

lemma xi_time_part60a_jensen_defect_radial_measure_inversion_hinge_forwardDifference
    (c t : ℤ) :
    xi_time_part60a_jensen_defect_radial_measure_inversion_hinge c (t + 1) -
        xi_time_part60a_jensen_defect_radial_measure_inversion_hinge c t =
      if c ≤ t then 1 else 0 := by
  unfold xi_time_part60a_jensen_defect_radial_measure_inversion_hinge
  split_ifs <;> omega

lemma xi_time_part60a_jensen_defect_radial_measure_inversion_hinge_secondDifference
    (c t : ℤ) :
    xi_time_part60a_jensen_defect_radial_measure_inversion_hinge c (t + 1) -
          2 * xi_time_part60a_jensen_defect_radial_measure_inversion_hinge c t +
        xi_time_part60a_jensen_defect_radial_measure_inversion_hinge c (t - 1) =
      if c = t then 1 else 0 := by
  unfold xi_time_part60a_jensen_defect_radial_measure_inversion_hinge
  split_ifs <;> omega

lemma xi_time_part60a_jensen_defect_radial_measure_inversion_potentialOf_forwardSlope
    (atoms : List xi_time_part60a_jensen_defect_radial_measure_inversion_atom) (t : ℤ) :
    xi_time_part60a_jensen_defect_radial_measure_inversion_potentialOf atoms (t + 1) -
        xi_time_part60a_jensen_defect_radial_measure_inversion_potentialOf atoms t =
      xi_time_part60a_jensen_defect_radial_measure_inversion_cumulativeOf atoms t := by
  induction atoms with
  | nil =>
      simp [xi_time_part60a_jensen_defect_radial_measure_inversion_potentialOf,
        xi_time_part60a_jensen_defect_radial_measure_inversion_cumulativeOf]
  | cons a atoms ih =>
      calc
        xi_time_part60a_jensen_defect_radial_measure_inversion_potentialOf (a :: atoms) (t + 1) -
            xi_time_part60a_jensen_defect_radial_measure_inversion_potentialOf (a :: atoms) t =
            (a.weight : ℤ) *
                (xi_time_part60a_jensen_defect_radial_measure_inversion_hinge a.radius (t + 1) -
                  xi_time_part60a_jensen_defect_radial_measure_inversion_hinge a.radius t) +
              (xi_time_part60a_jensen_defect_radial_measure_inversion_potentialOf atoms
                  (t + 1) -
                xi_time_part60a_jensen_defect_radial_measure_inversion_potentialOf atoms t) := by
              simp [xi_time_part60a_jensen_defect_radial_measure_inversion_potentialOf,
                xi_time_part60a_jensen_defect_radial_measure_inversion_atomPotential]
              ring
        _ =
            (a.weight : ℤ) * (if a.radius ≤ t then 1 else 0) +
              xi_time_part60a_jensen_defect_radial_measure_inversion_cumulativeOf atoms t := by
              rw [xi_time_part60a_jensen_defect_radial_measure_inversion_hinge_forwardDifference,
                ih]
        _ = xi_time_part60a_jensen_defect_radial_measure_inversion_cumulativeOf (a :: atoms) t := by
              by_cases h : a.radius ≤ t <;>
                simp [xi_time_part60a_jensen_defect_radial_measure_inversion_cumulativeOf, h]

lemma xi_time_part60a_jensen_defect_radial_measure_inversion_potentialOf_secondDifference
    (atoms : List xi_time_part60a_jensen_defect_radial_measure_inversion_atom) (t : ℤ) :
    xi_time_part60a_jensen_defect_radial_measure_inversion_potentialOf atoms (t + 1) -
          2 * xi_time_part60a_jensen_defect_radial_measure_inversion_potentialOf atoms t +
        xi_time_part60a_jensen_defect_radial_measure_inversion_potentialOf atoms (t - 1) =
      xi_time_part60a_jensen_defect_radial_measure_inversion_measureOf atoms t := by
  induction atoms with
  | nil =>
      simp [xi_time_part60a_jensen_defect_radial_measure_inversion_potentialOf,
        xi_time_part60a_jensen_defect_radial_measure_inversion_measureOf]
  | cons a atoms ih =>
      calc
        xi_time_part60a_jensen_defect_radial_measure_inversion_potentialOf (a :: atoms) (t + 1) -
              2 * xi_time_part60a_jensen_defect_radial_measure_inversion_potentialOf
                (a :: atoms) t +
            xi_time_part60a_jensen_defect_radial_measure_inversion_potentialOf (a :: atoms)
              (t - 1) =
            (a.weight : ℤ) *
                (xi_time_part60a_jensen_defect_radial_measure_inversion_hinge a.radius (t + 1) -
                    2 * xi_time_part60a_jensen_defect_radial_measure_inversion_hinge a.radius t +
                  xi_time_part60a_jensen_defect_radial_measure_inversion_hinge a.radius (t - 1)) +
              (xi_time_part60a_jensen_defect_radial_measure_inversion_potentialOf atoms
                    (t + 1) -
                  2 * xi_time_part60a_jensen_defect_radial_measure_inversion_potentialOf atoms t +
                xi_time_part60a_jensen_defect_radial_measure_inversion_potentialOf atoms
                  (t - 1)) := by
              simp [xi_time_part60a_jensen_defect_radial_measure_inversion_potentialOf,
                xi_time_part60a_jensen_defect_radial_measure_inversion_atomPotential]
              ring
        _ =
            (a.weight : ℤ) * (if a.radius = t then 1 else 0) +
              xi_time_part60a_jensen_defect_radial_measure_inversion_measureOf atoms t := by
              rw [xi_time_part60a_jensen_defect_radial_measure_inversion_hinge_secondDifference,
                ih]
        _ = xi_time_part60a_jensen_defect_radial_measure_inversion_measureOf (a :: atoms) t := by
              by_cases h : a.radius = t <;>
                simp [xi_time_part60a_jensen_defect_radial_measure_inversion_measureOf, h]

lemma xi_time_part60a_jensen_defect_radial_measure_inversion_measureOf_nonneg
    (atoms : List xi_time_part60a_jensen_defect_radial_measure_inversion_atom) (t : ℤ) :
    0 ≤ xi_time_part60a_jensen_defect_radial_measure_inversion_measureOf atoms t := by
  induction atoms with
  | nil =>
      simp [xi_time_part60a_jensen_defect_radial_measure_inversion_measureOf]
  | cons a atoms ih =>
      by_cases h : a.radius = t
      · have hw : (0 : ℤ) ≤ a.weight := by exact_mod_cast Nat.zero_le a.weight
        simp [xi_time_part60a_jensen_defect_radial_measure_inversion_measureOf, h,
          add_nonneg hw ih]
      · simpa [xi_time_part60a_jensen_defect_radial_measure_inversion_measureOf, h] using ih

/-- Paper label: `thm:xi-time-part60a-jensen-defect-radial-measure-inversion`. For a finite
ledger of weighted atoms on the integer log-radius line, the Jensen defect is the weighted hinge
potential, its first difference counts crossed zeros, and its second distributional difference
recovers exactly the radial atomic measure. -/
theorem paper_xi_time_part60a_jensen_defect_radial_measure_inversion
    (D : xi_time_part60a_jensen_defect_radial_measure_inversion_data) :
    D.jensenPotentialRepresentation ∧ D.convexPiecewiseAffine ∧ D.derivativeCountsZeros ∧
      D.secondDistributionDerivativeRecoversMeasure := by
  refine ⟨?representation, ?convex, ?derivative, ?second⟩
  · intro t
    rfl
  · constructor
    · intro t
      simp only [
        xi_time_part60a_jensen_defect_radial_measure_inversion_data.secondDifference,
        xi_time_part60a_jensen_defect_radial_measure_inversion_data.jensenPotential,
        xi_time_part60a_jensen_defect_radial_measure_inversion_potentialOf_secondDifference]
      exact xi_time_part60a_jensen_defect_radial_measure_inversion_measureOf_nonneg D.atoms t
    · intro t
      simp only [
        xi_time_part60a_jensen_defect_radial_measure_inversion_data.forwardSlope,
        xi_time_part60a_jensen_defect_radial_measure_inversion_data.jensenPotential,
        xi_time_part60a_jensen_defect_radial_measure_inversion_data.cumulativeZeroCount,
        xi_time_part60a_jensen_defect_radial_measure_inversion_potentialOf_forwardSlope]
  · intro t
    simp only [
      xi_time_part60a_jensen_defect_radial_measure_inversion_data.forwardSlope,
      xi_time_part60a_jensen_defect_radial_measure_inversion_data.jensenPotential,
      xi_time_part60a_jensen_defect_radial_measure_inversion_data.cumulativeZeroCount,
      xi_time_part60a_jensen_defect_radial_measure_inversion_potentialOf_forwardSlope]
  · intro t
    simp only [
      xi_time_part60a_jensen_defect_radial_measure_inversion_data.secondDifference,
      xi_time_part60a_jensen_defect_radial_measure_inversion_data.jensenPotential,
      xi_time_part60a_jensen_defect_radial_measure_inversion_data.radialMeasure,
      xi_time_part60a_jensen_defect_radial_measure_inversion_potentialOf_secondDifference]

end Omega.Zeta
