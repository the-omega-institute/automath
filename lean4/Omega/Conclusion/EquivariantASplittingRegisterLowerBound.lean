import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The concrete readout space of `a`-subsets of a `k`-point register alphabet. -/
abbrev ASubsetRegister (k a : Nat) := {s : Finset (Fin k) // s.card = a}

lemma card_aSubsetRegister (k a : Nat) :
    Fintype.card (ASubsetRegister k a) = Nat.choose k a := by
  simp [ASubsetRegister]

/-- A concrete model of an equivariant `a`-splitting mechanism: a finite register type equipped
with a surjective readout into the `a`-subsets of `Fin k`. -/
structure EquivariantASplittingMechanism (k a : Nat) where
  Register : Type
  instFintypeRegister : Fintype Register
  readout : Register → ASubsetRegister k a
  surjective_readout : Function.Surjective readout

attribute [instance] EquivariantASplittingMechanism.instFintypeRegister

/-- The number of register states used by the mechanism. -/
def EquivariantASplittingMechanism.registerCard {k a : Nat}
    (M : EquivariantASplittingMechanism k a) : Nat :=
  Fintype.card M.Register

/-- The canonical mechanism with register states indexed by the `a`-subsets themselves. -/
def canonicalEquivariantASplittingMechanism (k a : Nat) :
    EquivariantASplittingMechanism k a where
  Register := ASubsetRegister k a
  instFintypeRegister := inferInstance
  readout := id
  surjective_readout := by
    intro s
    exact ⟨s, rfl⟩

lemma register_lower_bound_of_surjective_readout {k a : Nat}
    (M : EquivariantASplittingMechanism k a) :
    Nat.choose k a ≤ M.registerCard := by
  have hcard : Fintype.card (ASubsetRegister k a) ≤ Fintype.card M.Register :=
    Fintype.card_le_of_surjective M.readout M.surjective_readout
  simpa [EquivariantASplittingMechanism.registerCard, card_aSubsetRegister] using hcard

/-- Paper label: `thm:conclusion-equivariant-a-splitting-register-lower-bound`.
Any equivariant `a`-splitting mechanism has at least `Nat.choose k a` states, and the canonical
subset register attains the bound. -/
theorem paper_conclusion_equivariant_a_splitting_register_lower_bound {k a : Nat} (_ha1 : 1 <= a)
    (_hak : a <= k - 1) :
    (forall M : EquivariantASplittingMechanism k a, Nat.choose k a <= M.registerCard) /\
      (exists M : EquivariantASplittingMechanism k a, M.registerCard = Nat.choose k a) := by
  refine ⟨register_lower_bound_of_surjective_readout, ?_⟩
  refine ⟨canonicalEquivariantASplittingMechanism k a, ?_⟩
  change Fintype.card (ASubsetRegister k a) = Nat.choose k a
  exact card_aSubsetRegister k a

end Omega.Conclusion
