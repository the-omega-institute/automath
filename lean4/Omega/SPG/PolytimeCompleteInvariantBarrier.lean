namespace Omega.SPG

/-- Chapter-local package for the complete-invariant barrier. The data record the polynomial-time
computability of the invariant, the reduction of `UNSAT` to comparison with a fixed unsatisfiable
formula, and the standard complexity-theoretic consequences. -/
structure PolytimeCompleteInvariantBarrierData where
  invariantComputableInPolynomialTime : Prop
  completeInvariant : Prop
  fixedUnsatisfiableFormula : Prop
  unsatReducesToInvariantEquality : Prop
  unsatInP : Prop
  satInP : Prop
  pEqualsNp : Prop
  deriveUnsatReduction :
    completeInvariant → fixedUnsatisfiableFormula → unsatReducesToInvariantEquality
  deriveUnsatInP :
    invariantComputableInPolynomialTime → unsatReducesToInvariantEquality → unsatInP
  deriveSatInP :
    unsatInP → satInP
  derivePEqualsNP :
    satInP → pEqualsNp

/-- Paper-facing wrapper for the resource-bounded complete-invariant obstruction: comparing the
invariant of a formula with the invariant of a fixed contradiction decides `UNSAT` in polynomial
time, hence also `SAT`, and therefore forces `P = NP`.
    thm:spg-polytime-complete-invariant-implies-p-equals-np -/
theorem paper_spg_polytime_complete_invariant_implies_p_equals_np
    (D : PolytimeCompleteInvariantBarrierData)
    (hPoly : D.invariantComputableInPolynomialTime) (hComplete : D.completeInvariant)
    (hBottom : D.fixedUnsatisfiableFormula) :
    D.unsatReducesToInvariantEquality ∧ D.unsatInP ∧ D.satInP ∧ D.pEqualsNp := by
  have hUnsatReduction : D.unsatReducesToInvariantEquality :=
    D.deriveUnsatReduction hComplete hBottom
  have hUnsatInP : D.unsatInP :=
    D.deriveUnsatInP hPoly hUnsatReduction
  have hSatInP : D.satInP :=
    D.deriveSatInP hUnsatInP
  exact ⟨hUnsatReduction, hUnsatInP, hSatInP, D.derivePEqualsNP hSatInP⟩

end Omega.SPG
