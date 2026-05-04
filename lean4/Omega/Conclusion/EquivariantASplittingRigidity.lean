import Omega.Conclusion.EquivariantASplittingRegisterLowerBound

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-equivariant-a-splitting-rigidity`. -/
theorem paper_conclusion_equivariant_a_splitting_rigidity {k a : Nat} (_ha1 : 1 <= a)
    (_hak : a <= k - 1) (M : EquivariantASplittingMechanism k a)
    (hcard : M.registerCard = Nat.choose k a) :
    Function.Bijective M.readout ∧
      (canonicalEquivariantASplittingMechanism k a).registerCard = M.registerCard := by
  have hdomain :
      Fintype.card M.Register = Fintype.card (ASubsetRegister k a) := by
    simpa [EquivariantASplittingMechanism.registerCard, card_aSubsetRegister] using hcard
  have hbij : Function.Bijective M.readout :=
    (Fintype.bijective_iff_surjective_and_card M.readout).2
      ⟨M.surjective_readout, hdomain⟩
  have hcanonical :
      (canonicalEquivariantASplittingMechanism k a).registerCard = Nat.choose k a := by
    change Fintype.card (ASubsetRegister k a) = Nat.choose k a
    exact card_aSubsetRegister k a
  exact ⟨hbij, hcanonical.trans hcard.symm⟩

end Omega.Conclusion
