import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete terminal-envelope package for solenoid maps over a fixed base projection. -/
structure conclusion_boundary_solenoid_over_base_rigidity_Data where
  Space : Type
  Base : Type
  projection : Space → Base
  terminal_unique :
    ∀ f : Space → Space, (∀ x, projection (f x) = projection x) → ∀ x, f x = x

namespace conclusion_boundary_solenoid_over_base_rigidity_Data

/-- Endomorphisms of the envelope. -/
structure Endomorphism (D : conclusion_boundary_solenoid_over_base_rigidity_Data) where
  map : D.Space → D.Space

instance (D : conclusion_boundary_solenoid_over_base_rigidity_Data) :
    CoeFun D.Endomorphism (fun _ => D.Space → D.Space) where
  coe u := u.map

/-- The identity endomorphism over the base. -/
def identity (D : conclusion_boundary_solenoid_over_base_rigidity_Data) : D.Endomorphism :=
  ⟨id⟩

/-- An endomorphism commutes with the base projection. -/
def CommutesWithBase (D : conclusion_boundary_solenoid_over_base_rigidity_Data)
    (u : D.Endomorphism) : Prop :=
  ∀ x, D.projection (u x) = D.projection x

@[ext]
theorem Endomorphism.ext {D : conclusion_boundary_solenoid_over_base_rigidity_Data}
    {u v : D.Endomorphism} (h : ∀ x, u x = v x) : u = v := by
  cases u
  cases v
  simp only [Endomorphism.mk.injEq]
  exact funext h

end conclusion_boundary_solenoid_over_base_rigidity_Data

/-- Paper label: `cor:conclusion-boundary-solenoid-over-base-rigidity`. -/
theorem paper_conclusion_boundary_solenoid_over_base_rigidity
    (D : conclusion_boundary_solenoid_over_base_rigidity_Data) (u : D.Endomorphism)
    (hu : D.CommutesWithBase u) : u = D.identity := by
  ext x
  simpa [conclusion_boundary_solenoid_over_base_rigidity_Data.identity] using
    D.terminal_unique (fun y => u y) hu x

end Omega.Conclusion
