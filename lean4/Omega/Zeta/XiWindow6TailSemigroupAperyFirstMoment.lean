import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Omega.Zeta.XiWindow6TailSemigroupCongruenceInvolution

namespace Omega.Zeta

/-- The Apéry representatives `34 * ((13 * r) % 21)` are indexed by a permutation of the residue
classes modulo `21`, so their first moment is `34` times the sum of all residues.
    prop:xi-window6-apery-first-moment -/
theorem paper_xi_window6_apery_first_moment :
    Finset.sum (Finset.range 21) (fun r => 34 * ((13 * r) % 21)) = 7140 := by
  native_decide

end Omega.Zeta
