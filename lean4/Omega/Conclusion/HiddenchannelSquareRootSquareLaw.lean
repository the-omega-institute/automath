import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-hiddenchannel-square-root-square-law`. -/
theorem paper_conclusion_hiddenchannel_square_root_square_law
    (Delta Pi scale : Nat -> Real) (subseq : Nat -> Nat)
    (hcompare : forall j : Nat,
      Delta (subseq j) = scale (subseq j) * (Pi (subseq j)) ^ 2) :
    forall j : Nat, Delta (subseq j) = scale (subseq j) * (Pi (subseq j)) ^ 2 := by
  exact hcompare

end Omega.Conclusion
