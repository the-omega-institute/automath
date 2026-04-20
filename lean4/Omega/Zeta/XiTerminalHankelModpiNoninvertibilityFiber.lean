import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper package: determinant vanishing modulo `π^t` yields a nontrivial kernel, and any such
kernel produces an affine fiber of solutions. The theorem records the two-step implication chain
used in the text.
    prop:xi-terminal-hankel-modpi-noninvertibility-fiber -/
theorem paper_xi_terminal_hankel_modpi_noninvertibility_fiber
    (detVanishesMod nontrivialKernel affineSolutionFiber : Nat -> Prop) :
    (∀ t : Nat, detVanishesMod t -> nontrivialKernel t) ->
      (∀ t : Nat, nontrivialKernel t -> affineSolutionFiber t) ->
      ∀ t : Nat, detVanishesMod t -> nontrivialKernel t ∧ affineSolutionFiber t := by
  intro hKernel hAffine t hDet
  refine ⟨hKernel t hDet, ?_⟩
  exact hAffine t (hKernel t hDet)

end Omega.Zeta
