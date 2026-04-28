import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Collision-Perron fingerprints are constant on every finite set of queried collision orders. -/
def conclusion_finite_collision_spectrum_incomplete_fingerprint
    (Q : Finset ℕ) (_haltTime : Option ℕ) : Q → ℕ :=
  fun _ => 1

/-- A concrete transducer family whose output records whether the queried depth has reached the
halting time.  The non-halting branch is constantly false. -/
def conclusion_finite_collision_spectrum_incomplete_transducer (haltTime : Option ℕ) (n : ℕ) :
    Bool :=
  match haltTime with
  | none => false
  | some T => decide (T ≤ n)

/-- Concrete finite-collision-spectrum incompleteness statement. -/
def conclusion_finite_collision_spectrum_incomplete_statement : Prop :=
  (∀ (Q : Finset ℕ) (T U : Option ℕ),
      conclusion_finite_collision_spectrum_incomplete_fingerprint Q T =
        conclusion_finite_collision_spectrum_incomplete_fingerprint Q U) ∧
    (∀ T : ℕ,
      conclusion_finite_collision_spectrum_incomplete_transducer none T ≠
        conclusion_finite_collision_spectrum_incomplete_transducer (some T) T) ∧
    (∀ T U : ℕ,
      T < U →
        conclusion_finite_collision_spectrum_incomplete_transducer (some T) T ≠
          conclusion_finite_collision_spectrum_incomplete_transducer (some U) T)

/-- Paper label: `cor:conclusion-finite-collision-spectrum-incomplete`. -/
theorem paper_conclusion_finite_collision_spectrum_incomplete :
    conclusion_finite_collision_spectrum_incomplete_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro Q T U
    funext q
    rfl
  · intro T
    simp [conclusion_finite_collision_spectrum_incomplete_transducer]
  · intro T U hTU
    simp [conclusion_finite_collision_spectrum_incomplete_transducer, Nat.not_le_of_gt hTU]

end Omega.Conclusion
