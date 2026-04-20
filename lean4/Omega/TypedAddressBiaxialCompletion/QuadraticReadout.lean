import Mathlib.Tactic

namespace Omega.TypedAddressBiaxialCompletion

/-- Concrete data for a projective quadratic readout: an address space, a real amplitude lift, and
an orientation choice implementing the gauge action by sign. The readout is the Born-style square
of the amplitude, so changing sign does not alter the observed value. -/
structure QuadraticReadoutData where
  Address : Type
  lift : Address → ℝ
  orientation : Address → Bool

namespace QuadraticReadoutData

/-- A representative of the projective class, obtained by flipping the sign according to the local
gauge choice. -/
def signedLift (D : QuadraticReadoutData) (a : D.Address) : ℝ :=
  if D.orientation a then D.lift a else -D.lift a

/-- The quadratic form used for the readout. -/
def quadraticForm (_D : QuadraticReadoutData) (x : ℝ) : ℝ :=
  x ^ 2

/-- The readout seen on the lifted amplitudes. -/
def readout (D : QuadraticReadoutData) (a : D.Address) : ℝ :=
  D.quadraticForm (D.lift a)

/-- Passing from a lift to its projective class does not change the quadratic readout. -/
def projectiveReadoutWellDefined (D : QuadraticReadoutData) : Prop :=
  ∀ a, D.quadraticForm (D.signedLift a) = D.readout a

/-- The amplitudes are already realized on the carrier `ℝ`. -/
def hasAmplitudeRealization (D : QuadraticReadoutData) : Prop :=
  ∃ amp : D.Address → ℝ, ∀ a, D.readout a = D.quadraticForm (amp a)

/-- Squaring is positive semidefinite on the real carrier. -/
def hasPositiveSemidefiniteQuadraticForm (D : QuadraticReadoutData) : Prop :=
  ∀ x : ℝ, 0 ≤ D.quadraticForm x

/-- The readout factors through the quadratic form after passing to a projective representative. -/
def readoutFactorsThroughQuadraticForm (D : QuadraticReadoutData) : Prop :=
  ∃ amp : D.Address → ℝ, ∀ a, D.readout a = D.quadraticForm (amp a)

end QuadraticReadoutData

/-- A sign gauge acts trivially on the quadratic readout, the amplitudes are realized on `ℝ`, the
square form is positive semidefinite, and the readout factors through that quadratic form.
    prop:typed-address-biaxial-completion-quadratic-readout -/
theorem paper_typed_address_biaxial_completion_quadratic_readout (D : QuadraticReadoutData) :
    D.projectiveReadoutWellDefined ∧ D.hasAmplitudeRealization ∧
      D.hasPositiveSemidefiniteQuadraticForm ∧ D.readoutFactorsThroughQuadraticForm := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    by_cases h : D.orientation a
    · simp [QuadraticReadoutData.signedLift, QuadraticReadoutData.readout,
        QuadraticReadoutData.quadraticForm, h]
    · simp [QuadraticReadoutData.signedLift, QuadraticReadoutData.readout,
        QuadraticReadoutData.quadraticForm, h]
  · refine ⟨D.lift, ?_⟩
    intro a
    rfl
  · intro x
    exact sq_nonneg x
  · refine ⟨D.signedLift, ?_⟩
    intro a
    by_cases h : D.orientation a
    · simp [QuadraticReadoutData.signedLift, QuadraticReadoutData.readout,
        QuadraticReadoutData.quadraticForm, h]
    · simp [QuadraticReadoutData.signedLift, QuadraticReadoutData.readout,
        QuadraticReadoutData.quadraticForm, h]

end Omega.TypedAddressBiaxialCompletion
