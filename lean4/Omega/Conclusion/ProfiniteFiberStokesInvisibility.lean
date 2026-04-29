import Mathlib.Data.Real.Basic

namespace Omega.Conclusion

/-- Concrete profinite-fiber package for functorial Stokes invisibility.  The fiber map, boundary
operators, and linear functionals are explicit objects; the compatibility fields are the functorial
identities used to transport the base Stokes identity to the pullback fiber. -/
structure conclusion_profinite_fiber_stokes_invisibility_data where
  conclusion_profinite_fiber_stokes_invisibility_base : Type
  conclusion_profinite_fiber_stokes_invisibility_fiber : Type
  conclusion_profinite_fiber_stokes_invisibility_projection :
    conclusion_profinite_fiber_stokes_invisibility_fiber →
      conclusion_profinite_fiber_stokes_invisibility_base
  conclusion_profinite_fiber_stokes_invisibility_boundaryBase :
    (conclusion_profinite_fiber_stokes_invisibility_base → ℝ) →
      conclusion_profinite_fiber_stokes_invisibility_base → ℝ
  conclusion_profinite_fiber_stokes_invisibility_boundaryFiber :
    (conclusion_profinite_fiber_stokes_invisibility_fiber → ℝ) →
      conclusion_profinite_fiber_stokes_invisibility_fiber → ℝ
  conclusion_profinite_fiber_stokes_invisibility_integralBase :
    (conclusion_profinite_fiber_stokes_invisibility_base → ℝ) → ℝ
  conclusion_profinite_fiber_stokes_invisibility_integralFiber :
    (conclusion_profinite_fiber_stokes_invisibility_fiber → ℝ) → ℝ
  conclusion_profinite_fiber_stokes_invisibility_boundaryCompatibility :
    ∀ f : conclusion_profinite_fiber_stokes_invisibility_base → ℝ,
      conclusion_profinite_fiber_stokes_invisibility_boundaryFiber
          (fun x =>
            f (conclusion_profinite_fiber_stokes_invisibility_projection x)) =
        fun x =>
          conclusion_profinite_fiber_stokes_invisibility_boundaryBase f
            (conclusion_profinite_fiber_stokes_invisibility_projection x)
  conclusion_profinite_fiber_stokes_invisibility_pullbackIntegral :
    ∀ f : conclusion_profinite_fiber_stokes_invisibility_base → ℝ,
      conclusion_profinite_fiber_stokes_invisibility_integralFiber
          (fun x =>
            f (conclusion_profinite_fiber_stokes_invisibility_projection x)) =
        conclusion_profinite_fiber_stokes_invisibility_integralBase f
  conclusion_profinite_fiber_stokes_invisibility_baseStokes :
    ∀ f : conclusion_profinite_fiber_stokes_invisibility_base → ℝ,
      conclusion_profinite_fiber_stokes_invisibility_integralBase
          (conclusion_profinite_fiber_stokes_invisibility_boundaryBase f) =
        0

namespace conclusion_profinite_fiber_stokes_invisibility_data

/-- Pullback of a base cochain to the profinite fiber. -/
def pullback (D : conclusion_profinite_fiber_stokes_invisibility_data)
    (f : D.conclusion_profinite_fiber_stokes_invisibility_base → ℝ) :
    D.conclusion_profinite_fiber_stokes_invisibility_fiber → ℝ :=
  fun x => f (D.conclusion_profinite_fiber_stokes_invisibility_projection x)

/-- The fiber Stokes integral vanishes for pullbacks from the base. -/
def stokesIdentity (D : conclusion_profinite_fiber_stokes_invisibility_data) : Prop :=
  ∀ f : D.conclusion_profinite_fiber_stokes_invisibility_base → ℝ,
    D.conclusion_profinite_fiber_stokes_invisibility_integralFiber
        (D.conclusion_profinite_fiber_stokes_invisibility_boundaryFiber (D.pullback f)) =
      0

/-- Pullback cochains on the fiber only depend on the base projection. -/
def dependsOnlyOnBaseProjection
    (D : conclusion_profinite_fiber_stokes_invisibility_data) : Prop :=
  ∀ (f : D.conclusion_profinite_fiber_stokes_invisibility_base → ℝ)
    (x y : D.conclusion_profinite_fiber_stokes_invisibility_fiber),
    D.conclusion_profinite_fiber_stokes_invisibility_projection x =
        D.conclusion_profinite_fiber_stokes_invisibility_projection y →
      D.pullback f x = D.pullback f y

end conclusion_profinite_fiber_stokes_invisibility_data

/-- Paper label: `thm:conclusion-profinite-fiber-stokes-invisibility`. -/
theorem paper_conclusion_profinite_fiber_stokes_invisibility
    (D : conclusion_profinite_fiber_stokes_invisibility_data) :
    D.stokesIdentity ∧ D.dependsOnlyOnBaseProjection := by
  constructor
  · intro f
    change
      D.conclusion_profinite_fiber_stokes_invisibility_integralFiber
          (D.conclusion_profinite_fiber_stokes_invisibility_boundaryFiber
            (fun x => f (D.conclusion_profinite_fiber_stokes_invisibility_projection x))) =
        0
    rw [D.conclusion_profinite_fiber_stokes_invisibility_boundaryCompatibility f]
    rw [D.conclusion_profinite_fiber_stokes_invisibility_pullbackIntegral
      (D.conclusion_profinite_fiber_stokes_invisibility_boundaryBase f)]
    exact D.conclusion_profinite_fiber_stokes_invisibility_baseStokes f
  · intro f x y hxy
    simp [conclusion_profinite_fiber_stokes_invisibility_data.pullback, hxy]

end Omega.Conclusion
