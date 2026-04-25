import Omega.SyncKernelRealInput.GMProfiniteHaarDichotomy

namespace Omega.SyncKernelRealInput

/-- Paper label: `prop:gm-affine-near-closure-profinite-degeneracy`. The affine near-closure
obstruction is formalized as the negation of the Haar branch in the profinite Haar dichotomy. -/
theorem paper_gm_affine_near_closure_profinite_degeneracy
    (D : gm_profinite_haar_dichotomy_data)
    (hDichotomy : D.profiniteHaarLimit ∨ ∃ q : ℕ, 2 ≤ q ∧ D.cosetDegenerate q)
    (hNearClosureNotHaar : ¬ D.profiniteHaarLimit) :
    ∃ q : ℕ, 2 ≤ q ∧ D.cosetDegenerate q := by
  rcases hDichotomy with hHaar | hDegenerate
  · exact False.elim (hNearClosureNotHaar hHaar)
  · exact hDegenerate

end Omega.SyncKernelRealInput
