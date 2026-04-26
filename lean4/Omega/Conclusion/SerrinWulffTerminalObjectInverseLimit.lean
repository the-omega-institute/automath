import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.VisiblePhaseLift

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-serrin-wulff-terminal-object-inverse-limit`.
If the normalized realizable class is the singleton `{W_K}`, then any restriction-compatible
finite-level coding of `W_K` determines a unique inverse-limit point, and every normalized
realizable object has those same coordinates. -/
theorem paper_conclusion_serrin_wulff_terminal_object_inverse_limit
    {n : ℕ} (WK : Fin n → ℝ)
    (X : Nat → Type) (pi : ∀ {hi lo : Nat}, lo ≤ hi → X hi → X lo)
    (hpi : Omega.TypedAddressBiaxialCompletion.IsInverseSystem X pi)
    (code : ∀ m : Nat, (Fin n → ℝ) → X m)
    (hcode : ∀ {hi lo : Nat} (h : lo ≤ hi), pi h (code hi WK) = code lo WK) :
    let normalizedClass : Set (Fin n → ℝ) := {Ω | Ω = WK}
    ∃! u : Omega.TypedAddressBiaxialCompletion.InverseLimit X pi,
      ∀ Ω ∈ normalizedClass, ∀ m : Nat, u.1 m = code m Ω := by
  dsimp
  obtain ⟨u, hu, hu_unique⟩ :=
    Omega.TypedAddressBiaxialCompletion.paper_typed_address_biaxial_completion_visible_phase_lift
      X pi hpi (fun m => code m WK) (fun {hi lo} h => hcode h)
  refine ⟨u, ?_, ?_⟩
  · intro Ω hΩ m
    rcases hΩ with rfl
    exact hu m
  · intro v hv
    apply hu_unique
    intro m
    have hWK : WK ∈ ({Ω : Fin n → ℝ | Ω = WK} : Set (Fin n → ℝ)) := by
      simp
    simpa using hv WK hWK m

end Omega.Conclusion
