import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic
import Omega.Zeta.SyncCyclotomicDegreeLaw

namespace Omega.Zeta

open Polynomial

/-- Paper-facing evenness wrapper for the cyclotomic elimination polynomial in the even-modulus
case: symmetry under `w ↦ -w`, membership in `ℤ[w²]`, and the halved degree law.
    prop:sync-cyclotomic-elimination-evenness -/
theorem paper_sync_cyclotomic_elimination_evenness
    (m : ℕ) (_hm : 4 ≤ m) (heven : Even m)
    (R : Polynomial ℤ)
    (hSymm : ∀ z : ℤ, R.eval (-z) = R.eval z)
    (hSquare : ∃ S : Polynomial ℤ, R = S.comp (X ^ 2))
    (hDegree : R.natDegree = 3 * Nat.totient (2 * m)) :
    (∀ z : ℤ, R.eval (-z) = R.eval z) ∧
    (∃ S : Polynomial ℤ, R = S.comp (X ^ 2)) ∧
    R.natDegree = 6 * Nat.totient m ∧
    R.natDegree / 2 = 3 * Nat.totient m := by
  have hDegreeEven : R.natDegree = 6 * Nat.totient m := by
    rw [hDegree, Nat.totient_two_mul_of_even heven]
    ring
  refine ⟨hSymm, hSquare, hDegreeEven, ?_⟩
  rw [hDegreeEven]
  omega

end Omega.Zeta
