import Omega.Folding.ModSemiringsUnitalAutomorphismRigidity

namespace Omega

/-- The visible unital semiring on the finite-resolution quotient has no nontrivial symmetry:
every automorphism of `ZMod (F_{m+2})` is the identity, so the automorphism type is subsingleton.
    `cor:fold-visible-unital-semirings-no-nontrivial-symmetry` -/
theorem paper_fold_visible_unital_semirings_no_nontrivial_symmetry (m : Nat) :
    Subsingleton (ZMod (Nat.fib (m + 2)) ≃+* ZMod (Nat.fib (m + 2))) := by
  refine ⟨?_⟩
  intro σ τ
  rw [paper_fold_mod_semirings_unital_automorphism_rigidity m σ,
    paper_fold_mod_semirings_unital_automorphism_rigidity m τ]

end Omega
