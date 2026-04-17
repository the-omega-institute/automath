import Mathlib.Tactic

namespace Omega.Folding

/-- Paper: `thm:fold-bernoulli-p-regeneration-length-pgf-recurrence-tail`. -/
theorem paper_fold_bernoulli_p_regeneration_length_pgf_recurrence_tail
    (rationalPgf tailRecurrence simpleRoots exponentialTail : Prop) (hPgf : rationalPgf)
    (hRec : rationalPgf → tailRecurrence) (hRoots : tailRecurrence → simpleRoots)
    (hTail : simpleRoots → exponentialTail) :
    rationalPgf ∧ tailRecurrence ∧ simpleRoots ∧ exponentialTail := by
  refine ⟨hPgf, hRec hPgf, hRoots (hRec hPgf), hTail (hRoots (hRec hPgf))⟩

end Omega.Folding
