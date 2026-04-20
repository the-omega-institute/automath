import Mathlib.Tactic
import Omega.GU.TerminalGamma6Rigidity

namespace Omega.GU

/-- Repackage the paper rigidity wrapper as the explicit statement that every adjacency-preserving
permutation of `Γ₆` is trivial. -/
private theorem terminalGamma6_automorphism_group_trivial
    {X : Type*} (Adj : X → X → Prop)
    (hRigid : ∀ tau : Equiv.Perm X,
      (∀ a b, Adj a b ↔ Adj (tau a) (tau b)) → tau = Equiv.refl X) :
    ∀ tau : Equiv.Perm X, (∀ a b, Adj a b ↔ Adj (tau a) (tau b)) → tau = Equiv.refl X := by
  let h : TerminalGamma6RigidityData :=
    { graphConnected := True
      automorphismGroupTrivial := ∀ tau : Equiv.Perm X,
        (∀ a b, Adj a b ↔ Adj (tau a) (tau b)) → tau = Equiv.refl X
      finiteRigidityCertificate := True
      certificate := trivial
      connected_of_certificate := fun _ => trivial
      rigid_of_certificate := fun _ => hRigid }
  exact (paper_terminal_gamma6_rigidity h).2

/-- Any group action on the terminal window-`6` type set that preserves the adjacency graph
`Γ₆` factors through `Aut(Γ₆)`, hence is trivial once `Aut(Γ₆) = 1`.
    cor:terminal-gamma6-no-continuous-nonabelian-symmetry -/
theorem paper_terminal_gamma6_no_continuous_nonabelian_symmetry
    {G X : Type*} [Group G] [MulAction G X] (Adj : X → X → Prop)
    (hRigid : ∀ tau : Equiv.Perm X,
      (∀ a b, Adj a b ↔ Adj (tau a) (tau b)) → tau = Equiv.refl X)
    (hAdj : ∀ g : G, ∀ a b : X, Adj a b ↔ Adj (g • a) (g • b)) :
    ∀ g : G, ∀ x : X, g • x = x := by
  have hAut :=
    terminalGamma6_automorphism_group_trivial (Adj := Adj) hRigid
  intro g x
  have hperm : MulAction.toPerm g = Equiv.refl X := by
    apply hAut (MulAction.toPerm g)
    intro a b
    simpa using hAdj g a b
  have hx := congrArg (fun e : Equiv.Perm X => e x) hperm
  simpa using hx

end Omega.GU
