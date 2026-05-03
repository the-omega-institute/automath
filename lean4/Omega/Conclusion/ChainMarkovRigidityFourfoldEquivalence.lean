namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-chain-markov-rigidity-fourfold-equivalence`. -/
theorem paper_conclusion_chain_markov_rigidity_fourfold_equivalence
    (loopZero detIdentity eqMarkov inverseTridiagonal : Prop)
    (h12 : loopZero ↔ detIdentity) (h13 : loopZero ↔ eqMarkov)
    (h34 : eqMarkov ↔ inverseTridiagonal) :
    (loopZero ↔ detIdentity) ∧ (detIdentity ↔ eqMarkov) ∧
      (eqMarkov ↔ inverseTridiagonal) ∧ (inverseTridiagonal ↔ loopZero) := by
  refine ⟨h12, ?_, h34, ?_⟩
  · exact h12.symm.trans h13
  · exact h34.symm.trans h13.symm

end Omega.Conclusion
