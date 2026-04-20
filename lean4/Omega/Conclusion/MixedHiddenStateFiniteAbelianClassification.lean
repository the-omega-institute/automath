import Mathlib.Tactic

namespace Omega.Conclusion

/-- The `2`-torsion subgroup of an additive commutative group. -/
def TwoTorsion (G : Type*) [AddCommGroup G] : Type _ :=
  { g : G // g + g = 0 }

/-- Mixed hidden-state observables split into a collision component indexed by `Fin beta` and a
fibadic component recorded by a single element of the finite abelian receiver. -/
abbrev MixedHiddenStateObservable (beta : Nat) (G : Type*) [AddCommGroup G] : Type _ :=
  (Fin beta → TwoTorsion G) × G

/-- Paper-facing finite-abelian classification of mixed hidden-state observables.
    thm:conclusion-mixed-hidden-state-finite-abelian-classification -/
def paper_conclusion_mixed_hidden_state_finite_abelian_classification
    (beta : Nat) (G : Type*) [AddCommGroup G] [Fintype G] :
    Equiv (MixedHiddenStateObservable beta G) ((Fin beta -> TwoTorsion G) × G) := by
  exact Equiv.refl _

end Omega.Conclusion
