import Mathlib.Tactic

namespace Omega.GU

/-- If a weighted adjacency matrix has positive entries exactly on the support graph and is
preserved by a permutation, then any rigidity statement for the support graph forces that
permutation to be trivial.
    cor:terminal-gamma6-multiplicity-rigidity -/
theorem paper_terminal_gamma6_multiplicity_rigidity {X : Type} (Adj : X → X → Prop)
    (A : X → X → Nat) (sigma : Equiv.Perm X)
    (hRigid : ∀ tau : Equiv.Perm X,
      (∀ a b, Adj a b ↔ Adj (tau a) (tau b)) → tau = Equiv.refl X)
    (hSupport : ∀ u v, 0 < A u v ↔ Adj u v)
    (hPres : ∀ u v, A (sigma u) (sigma v) = A u v) : sigma = Equiv.refl X := by
  apply hRigid sigma
  intro a b
  constructor
  · intro hab
    have hPos : 0 < A a b := (hSupport a b).2 hab
    have hPos' : 0 < A (sigma a) (sigma b) := by
      simpa [hPres a b] using hPos
    exact (hSupport (sigma a) (sigma b)).1 hPos'
  · intro hsab
    have hPos' : 0 < A (sigma a) (sigma b) := (hSupport (sigma a) (sigma b)).2 hsab
    have hPos : 0 < A a b := by
      simpa [hPres a b] using hPos'
    exact (hSupport a b).1 hPos

end Omega.GU
