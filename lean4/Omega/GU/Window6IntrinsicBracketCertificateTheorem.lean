import Omega.GU.TerminalDeltaParityRule
import Omega.GU.TerminalGamma6Rigidity
import Omega.GU.Window6IntrinsicBracketFiniteIntegerReduction
import Omega.GU.Window6RootDictionaryPullbackBracket

namespace Omega.GU

/-- Package the root-dictionary pullback bracket, the finite-integer reduction, the terminal
`δ = 34` parity certificate, and the terminal `Γ₆` rigidity audit into one paper-facing theorem.
    thm:window6-intrinsic-bracket-certificate-theorem -/
theorem paper_window6_intrinsic_bracket_certificate_theorem (V G : Type _)
    (bracketG : G → G → G) (phi : V → G) (psi : G → V) (h_left : ∀ v, psi (phi v) = v)
    (h_right : ∀ g, phi (psi g) = g) (D : Window6IntrinsicBracketFiniteIntegerReductionData)
    (R : TerminalGamma6RigidityData) :
    (∃ bracketV : V → V → V, ∀ x y, phi (bracketV x y) = bracketG (phi x) (phi y)) ∧
      (D.intrinsicBracketExistsUnique ↔ D.finiteIntegerSystemHasUniqueSolution) ∧
      (Nat.fib 9 = 34 ∧ terminalFoldbin6BoundaryOffsets = ({34} : Finset Nat)) ∧
      R.automorphismGroupTrivial := by
  have hPullback :=
    paper_window6_root_dictionary_pullback_bracket V G bracketG phi psi h_left h_right
  have hReduction := paper_window6_intrinsic_bracket_finite_integer_reduction D
  rcases paper_terminal_delta_parity_rule with ⟨hFib, hOffsets, _, _, _⟩
  rcases paper_terminal_gamma6_rigidity R with ⟨_, hRigid⟩
  exact ⟨hPullback, hReduction, ⟨hFib, hOffsets⟩, hRigid⟩

end Omega.GU
