namespace Omega.GU

set_option maxHeartbeats 400000 in
/-- Transport the ambient operator-envelope bracket along an inverse pair.
    thm:pullback-bracket-from-operator-envelope -/
theorem paper_window6_pullback_bracket_from_operator_envelope (W V : Type _)
    (bracketV : V → V → V) (Phi : W → V) (Psi : V → W) (_h_left : ∀ w, Psi (Phi w) = w)
    (h_right : ∀ v, Phi (Psi v) = v) :
    ∃ bracketW : W → W → W, ∀ x y, Phi (bracketW x y) = bracketV (Phi x) (Phi y) := by
  let bracketW : W → W → W := fun x y => Psi (bracketV (Phi x) (Phi y))
  refine ⟨bracketW, ?_⟩
  intro x y
  dsimp [bracketW]
  exact h_right (bracketV (Phi x) (Phi y))

end Omega.GU
