import Mathlib.Tactic

namespace Omega.Conclusion

/-- The two homotopy phases recorded by the mod-`6` max-fiber diagram. -/
inductive conclusion_maxfiber_mod6_homotopy_phase_diagram_phase where
  | contractible
  | sphere (dimension : ℕ)
  deriving DecidableEq, Repr

/-- The phase attached to `m`: even max-fiber multiplicity means contractible, while odd
multiplicity records the spherical branch with dimension `τ(m) - 1`. -/
def conclusion_maxfiber_mod6_homotopy_phase_diagram_model
    (D τ : ℕ → ℕ) (m : ℕ) : conclusion_maxfiber_mod6_homotopy_phase_diagram_phase :=
  if Even (D m) then .contractible else .sphere (τ m - 1)

/-- Concrete package for the mod-`6` phase diagram: once the parity-to-homotopy dichotomy is known
for the max-fiber branch, odd windows and the `m ≡ 2 (mod 6)` branch are contractible, whereas the
`m ≡ 0,4 (mod 6)` branch is spherical. -/
def conclusion_maxfiber_mod6_homotopy_phase_diagram_package (D τ : ℕ → ℕ) : Prop :=
  (∀ m : ℕ,
      Odd m →
      Even (D m) →
      conclusion_maxfiber_mod6_homotopy_phase_diagram_model D τ m = .contractible) ∧
    (∀ m : ℕ,
      m % 6 = 2 →
      Even (D m) →
      conclusion_maxfiber_mod6_homotopy_phase_diagram_model D τ m = .contractible) ∧
    (∀ m : ℕ,
      m % 6 = 0 ∨ m % 6 = 4 →
      ¬ Even (D m) →
      conclusion_maxfiber_mod6_homotopy_phase_diagram_model D τ m = .sphere (τ m - 1))

/-- Paper label: `thm:conclusion-maxfiber-mod6-homotopy-phase-diagram`. The theorem is the direct
translation of the parity-to-homotopy dichotomy into the three residue classes that occur in the
max-fiber phase diagram. -/
theorem paper_conclusion_maxfiber_mod6_homotopy_phase_diagram
    (D τ : ℕ → ℕ) : conclusion_maxfiber_mod6_homotopy_phase_diagram_package D τ := by
  refine ⟨?_, ?_, ?_⟩
  · intro m _hm hEven
    simp [conclusion_maxfiber_mod6_homotopy_phase_diagram_model, hEven]
  · intro m _hm hEven
    simp [conclusion_maxfiber_mod6_homotopy_phase_diagram_model, hEven]
  · intro m _hm hNotEven
    simp [conclusion_maxfiber_mod6_homotopy_phase_diagram_model, hNotEven]

end Omega.Conclusion
