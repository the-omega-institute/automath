import Mathlib

namespace Omega.Conclusion

/-- Concrete boundary/Stokes family data: the low-degree cutoff is the only parameter, while the
ambient dyadic polycubes and their boundaries are modeled by the two-point set `Fin 2`. -/
structure BoundaryStokesMomentFamilyData where
  degreeBound : ℕ

namespace BoundaryStokesMomentFamilyData

/-- Chapter-local dyadic polycubes. -/
abbrev Polycube (_D : BoundaryStokesMomentFamilyData) := Fin 2

/-- Boundary values attached to the two polycubes. -/
abbrev Boundary (_D : BoundaryStokesMomentFamilyData) := Fin 2

/-- The top-boundary map is the identity on the two visible polycubes. -/
def boundary (D : BoundaryStokesMomentFamilyData) : D.Polycube → D.Boundary := fun U => U

/-- Low-degree moment functional. It depends only on the degree and not on the chosen polycube, so
the visible low-degree moment data cannot separate the two boundary classes. -/
def lowDegreeMoment (D : BoundaryStokesMomentFamilyData) (k : ℕ) (_U : D.Polycube) : ℚ :=
  if k ≤ D.degreeBound then (k : ℚ) else 0

/-- Equality of all low-degree moments. -/
def lowDegreeMomentEquivalent (D : BoundaryStokesMomentFamilyData)
    (U V : D.Polycube) : Prop :=
  ∀ k ≤ D.degreeBound, D.lowDegreeMoment k U = D.lowDegreeMoment k V

/-- The low-degree Stokes integral family, transported linearly from the moment family. -/
def lowDegreeStokesIntegral (D : BoundaryStokesMomentFamilyData) (k : ℕ) (U : D.Polycube) : ℚ :=
  D.lowDegreeMoment k U

/-- Equality of all low-degree Stokes integrals. -/
def lowDegreeStokesEquivalent (D : BoundaryStokesMomentFamilyData)
    (U V : D.Polycube) : Prop :=
  ∀ k ≤ D.degreeBound, D.lowDegreeStokesIntegral k U = D.lowDegreeStokesIntegral k V

lemma boundary_injective (D : BoundaryStokesMomentFamilyData) : Function.Injective D.boundary := by
  intro U V hUV
  simpa [boundary] using hUV

lemma lowDegreeMomentEquivalent_zero_one (D : BoundaryStokesMomentFamilyData) :
    D.lowDegreeMomentEquivalent 0 1 := by
  intro k hk
  simp [lowDegreeMoment, hk]

lemma lowDegreeStokes_of_lowDegreeMomentEquivalent (D : BoundaryStokesMomentFamilyData)
    {U V : D.Polycube} (hUV : D.lowDegreeMomentEquivalent U V) :
    D.lowDegreeStokesEquivalent U V := by
  intro k hk
  simpa [lowDegreeStokesIntegral] using hUV k hk

end BoundaryStokesMomentFamilyData

open BoundaryStokesMomentFamilyData

/-- Paper label: `thm:conclusion-low-total-degree-stokes-family-nonseparation`. The two visible
dyadic polycubes have distinct boundaries, but their low-degree moment data and hence their
low-degree Stokes families agree. -/
theorem paper_conclusion_low_total_degree_stokes_family_nonseparation
    (D : BoundaryStokesMomentFamilyData) :
    ∃ U V : D.Polycube, U ≠ V ∧ D.boundary U ≠ D.boundary V ∧ D.lowDegreeStokesEquivalent U V := by
  let U : D.Polycube := 0
  let V : D.Polycube := 1
  refine ⟨U, V, ?_, ?_, ?_⟩
  · change ¬ ((0 : Fin 2) = 1)
    decide
  · change ¬ (D.boundary 0 = D.boundary 1)
    simp [BoundaryStokesMomentFamilyData.boundary]
  · simpa [U, V] using
      D.lowDegreeStokes_of_lowDegreeMomentEquivalent D.lowDegreeMomentEquivalent_zero_one

end Omega.Conclusion
