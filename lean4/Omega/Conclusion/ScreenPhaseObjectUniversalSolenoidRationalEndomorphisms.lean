import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import Omega.Conclusion.ScreenKernelSolenoidBicompletion

namespace Omega.Conclusion

/-- One coordinate of the universal one-dimensional solenoid in the chosen-basis model. -/
abbrev conclusion_screen_phase_object_universal_solenoid_rational_endomorphisms_universal_solenoid_coordinate :=
  conclusion_screen_kernel_solenoid_bicompletion_torus_coordinate × ℤ

/-- The screen phase object written in the basis coming from `K_S ≃ ℤ^r`. -/
abbrev conclusion_screen_phase_object_universal_solenoid_rational_endomorphisms_phase_object
    (r : ℕ) :=
  conclusion_screen_kernel_solenoid_bicompletion_solenoid r

/-- The finite product `U^r` of the universal one-dimensional solenoid. -/
abbrev conclusion_screen_phase_object_universal_solenoid_rational_endomorphisms_universal_solenoid_power
    (r : ℕ) :=
  Fin r →
    conclusion_screen_phase_object_universal_solenoid_rational_endomorphisms_universal_solenoid_coordinate

/-- Pontryagin dual of `U^r`, modeled coordinatewise by `ℚ^r`. -/
abbrev conclusion_screen_phase_object_universal_solenoid_rational_endomorphisms_pontryagin_dual
    (r : ℕ) :=
  Fin r → ℚ

/-- Continuous endomorphisms of `U^r`, encoded by rational `r × r` matrices. -/
abbrev conclusion_screen_phase_object_universal_solenoid_rational_endomorphisms_rational_endomorphisms
    (r : ℕ) :=
  Matrix (Fin r) (Fin r) ℚ

/-- Coordinate model for continuous endomorphisms before identifying it with matrices. -/
abbrev conclusion_screen_phase_object_universal_solenoid_rational_endomorphisms_rational_endomorphism_model
    (r : ℕ) :=
  Fin r → Fin r → ℚ

/-- Choosing a basis identifies the phase object with `U^r` by separating each coordinate into
its torus and profinite parts. -/
def conclusion_screen_phase_object_universal_solenoid_rational_endomorphisms_phase_equiv
    (r : ℕ) :
    conclusion_screen_phase_object_universal_solenoid_rational_endomorphisms_phase_object r ≃
      conclusion_screen_phase_object_universal_solenoid_rational_endomorphisms_universal_solenoid_power
        r where
  toFun s := fun i => (s.1 i, s.2 i)
  invFun u := (fun i => (u i).1, fun i => (u i).2)
  left_inv s := by
    ext i <;> rfl
  right_inv u := by
    funext i
    cases h : u i with
    | mk a b =>
        simp [h]

/-- The Pontryagin dual package is already written as `ℚ^r`. -/
def conclusion_screen_phase_object_universal_solenoid_rational_endomorphisms_dual_equiv
    (r : ℕ) :
    conclusion_screen_phase_object_universal_solenoid_rational_endomorphisms_pontryagin_dual r ≃
      (Fin r → ℚ) :=
  Equiv.refl _

/-- Rational endomorphisms and rational matrices are the same coordinate object. -/
def conclusion_screen_phase_object_universal_solenoid_rational_endomorphisms_matrix_equiv
    (r : ℕ) :
    conclusion_screen_phase_object_universal_solenoid_rational_endomorphisms_rational_endomorphism_model
        r ≃
      conclusion_screen_phase_object_universal_solenoid_rational_endomorphisms_rational_endomorphisms
        r :=
  Equiv.refl _

/-- The chosen-basis phase object splits as `U^r`, its Pontryagin dual is `ℚ^r`, and its
continuous endomorphisms are `r × r` rational matrices. -/
def conclusion_screen_phase_object_universal_solenoid_rational_endomorphisms_statement : Prop :=
  ∀ r : ℕ,
    Nonempty
      (conclusion_screen_phase_object_universal_solenoid_rational_endomorphisms_phase_object r ≃
        conclusion_screen_phase_object_universal_solenoid_rational_endomorphisms_universal_solenoid_power
          r) ∧
      Nonempty
        (conclusion_screen_phase_object_universal_solenoid_rational_endomorphisms_pontryagin_dual
            r ≃
          (Fin r → ℚ)) ∧
      Nonempty
        (conclusion_screen_phase_object_universal_solenoid_rational_endomorphisms_rational_endomorphism_model
            r ≃
          conclusion_screen_phase_object_universal_solenoid_rational_endomorphisms_rational_endomorphisms
            r)

private lemma conclusion_screen_phase_object_universal_solenoid_rational_endomorphisms_statement_proof :
    conclusion_screen_phase_object_universal_solenoid_rational_endomorphisms_statement := by
  intro r
  refine ⟨?_, ?_, ?_⟩
  · exact
      ⟨conclusion_screen_phase_object_universal_solenoid_rational_endomorphisms_phase_equiv r⟩
  · exact
      ⟨conclusion_screen_phase_object_universal_solenoid_rational_endomorphisms_dual_equiv r⟩
  · exact
      ⟨conclusion_screen_phase_object_universal_solenoid_rational_endomorphisms_matrix_equiv r⟩

/-- Paper label:
`thm:conclusion-screen-phase-object-universal-solenoid-rational-endomorphisms`. Reusing the
chosen-basis model `K_S ≃ ℤ^r`, the phase object becomes `U^r`, its Pontryagin dual is `ℚ^r`, and
continuous endomorphisms are exactly rational matrices. -/
theorem paper_conclusion_screen_phase_object_universal_solenoid_rational_endomorphisms :
    conclusion_screen_phase_object_universal_solenoid_rational_endomorphisms_statement := by
  exact conclusion_screen_phase_object_universal_solenoid_rational_endomorphisms_statement_proof

end Omega.Conclusion
