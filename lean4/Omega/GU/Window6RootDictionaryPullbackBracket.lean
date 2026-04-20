import Omega.GU.PullbackBracketFromOperatorEnvelope

namespace Omega.GU

/-- Pull the operator-envelope bracket back along the window-`6` root-dictionary inverse pair. -/
theorem paper_window6_root_dictionary_pullback_bracket (V G : Type _)
    (bracketG : G → G → G) (phi : V → G) (psi : G → V) (h_left : ∀ v, psi (phi v) = v)
    (h_right : ∀ g, phi (psi g) = g) :
    ∃ bracketV : V → V → V, ∀ x y, phi (bracketV x y) = bracketG (phi x) (phi y) := by
  simpa using
    paper_window6_pullback_bracket_from_operator_envelope V G bracketG phi psi h_left h_right

end Omega.GU
