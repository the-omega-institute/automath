import Omega.Zeta.XiFoldCongruenceUnitalAutomorphismRigidity

namespace Omega.Zeta

/-- CRT/idempotent classification package for the concrete fold-congruence quotient. -/
def xi_fold_congruence_crt_primitive_idempotents_statement (s : ℕ) : Prop :=
  foldCongruenceEnd0ClassifiedByIdempotents s ∧
    foldCongruenceEnd0CountByPrimeSupport s ∧ foldCongruenceUnitalAutomorphismRigid s

/-- Paper label: `thm:xi-fold-congruence-crt-primitive-idempotents`.
The concrete residue-semiring model has the CRT prime-support idempotent count and the
corresponding rigidity package from the fold-congruence automorphism theorem. -/
theorem paper_xi_fold_congruence_crt_primitive_idempotents (s : ℕ) :
    xi_fold_congruence_crt_primitive_idempotents_statement s := by
  simpa [xi_fold_congruence_crt_primitive_idempotents_statement] using
    paper_xi_fold_congruence_unital_automorphism_rigidity s

end Omega.Zeta
