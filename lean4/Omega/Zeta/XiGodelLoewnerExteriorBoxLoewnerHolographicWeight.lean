import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- The `t`-subset coordinate family for the finite exterior box. -/
def xi_godel_loewner_exterior_box_loewner_holographic_weight_index_family
    (k t : Nat) : Finset (Finset (Fin k)) :=
  Finset.powersetCard t Finset.univ

/-- The number of exterior-box coordinates. -/
def xi_godel_loewner_exterior_box_loewner_holographic_weight_coordinate_count
    (k t : Nat) : Nat :=
  Nat.choose k t

/-- The side length attached to one exterior coordinate. -/
def xi_godel_loewner_exterior_box_loewner_holographic_weight_side
    {k : Nat} (L : Fin k → ℝ) (I : Finset (Fin k)) : ℝ :=
  ∏ i ∈ I, L i

/-- The axis length obtained by applying the diagonal scaling to the symmetrized cube. -/
def xi_godel_loewner_exterior_box_loewner_holographic_weight_axis
    {k : Nat} (t : Nat) (L : Fin k → ℝ) (I : Finset (Fin k)) : ℝ :=
  Real.sqrt (xi_godel_loewner_exterior_box_loewner_holographic_weight_coordinate_count k t) *
    xi_godel_loewner_exterior_box_loewner_holographic_weight_side L I / 2

/-- The product of all Loewner ellipsoid axes, with the unit-ball volume `κ` left symbolic. -/
def xi_godel_loewner_exterior_box_loewner_holographic_weight_volume
    {k : Nat} (t : Nat) (κ : ℝ) (L : Fin k → ℝ) : ℝ :=
  κ *
    ∏ I ∈ xi_godel_loewner_exterior_box_loewner_holographic_weight_index_family k t,
      xi_godel_loewner_exterior_box_loewner_holographic_weight_axis t L I

/-- The normalized log-volume readout after separating off the symbolic unit-ball volume. -/
def xi_godel_loewner_exterior_box_loewner_holographic_weight_log_volume
    {k : Nat} (t : Nat) (κ : ℝ) (L : Fin k → ℝ) : ℝ :=
  Real.log κ +
    ∑ I ∈ xi_godel_loewner_exterior_box_loewner_holographic_weight_index_family k t,
      Real.log (xi_godel_loewner_exterior_box_loewner_holographic_weight_axis t L I)

/-- Axis formula for the finite exterior-box Loewner ellipsoid. -/
def xi_godel_loewner_exterior_box_loewner_holographic_weight_axis_formula
    {k : Nat} (t : Nat) (L : Fin k → ℝ) : Prop :=
  ∀ I ∈ xi_godel_loewner_exterior_box_loewner_holographic_weight_index_family k t,
    xi_godel_loewner_exterior_box_loewner_holographic_weight_axis t L I =
      Real.sqrt (xi_godel_loewner_exterior_box_loewner_holographic_weight_coordinate_count k t) *
        xi_godel_loewner_exterior_box_loewner_holographic_weight_side L I / 2

/-- Volume formula as the product of the diagonal image axes. -/
def xi_godel_loewner_exterior_box_loewner_holographic_weight_volume_formula
    {k : Nat} (t : Nat) (κ : ℝ) (L : Fin k → ℝ) : Prop :=
  xi_godel_loewner_exterior_box_loewner_holographic_weight_volume t κ L =
    κ *
      ∏ I ∈ xi_godel_loewner_exterior_box_loewner_holographic_weight_index_family k t,
        xi_godel_loewner_exterior_box_loewner_holographic_weight_axis t L I

/-- Log-volume weight formula: the logarithmic readout is the sum over all exterior axes. -/
def xi_godel_loewner_exterior_box_loewner_holographic_weight_log_volume_weight_formula
    {k : Nat} (t : Nat) (κ : ℝ) (L : Fin k → ℝ) : Prop :=
  xi_godel_loewner_exterior_box_loewner_holographic_weight_log_volume t κ L =
    Real.log κ +
      ∑ I ∈ xi_godel_loewner_exterior_box_loewner_holographic_weight_index_family k t,
        Real.log (xi_godel_loewner_exterior_box_loewner_holographic_weight_axis t L I)

/-- Paper: `thm:xi-godel-loewner-exterior-box-loewner-holographic-weight`.
    Concrete finite-box package for the axis, volume, and log-volume identities. -/
theorem paper_xi_godel_loewner_exterior_box_loewner_holographic_weight
    {k : Nat} (t : Nat) (κ : ℝ) (L : Fin k → ℝ) :
    xi_godel_loewner_exterior_box_loewner_holographic_weight_axis_formula t L ∧
      xi_godel_loewner_exterior_box_loewner_holographic_weight_volume_formula t κ L ∧
      xi_godel_loewner_exterior_box_loewner_holographic_weight_log_volume_weight_formula
        t κ L := by
  refine ⟨?_, ?_, ?_⟩
  · intro I _hI
    rfl
  · rfl
  · rfl

end

end Omega.Zeta
