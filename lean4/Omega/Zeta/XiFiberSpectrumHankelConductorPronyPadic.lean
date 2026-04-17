import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Zeta.HankelDeterminantalRadicalEqRigidity

namespace Omega.Zeta

/-- Mod-`p` uniqueness criterion for the first Hankel block in the three-atom Prony problem. -/
def xiFiberPronyPadicUnique (p : ℕ) (w1 w2 w3 a1 a2 a3 : ℤ) : Prop :=
  ((hankel3 w1 w2 w3 a1 a2 a3).det : ZMod p) ≠ 0

/-- Integer obstruction detected by bad primes for the first Hankel block. -/
def xiFiberPronyPadicBadPrime (p : ℕ) (w1 w2 w3 a1 a2 a3 : ℤ) : Prop :=
  (p : ℤ) ∣ (hankel3 w1 w2 w3 a1 a2 a3).det

/-- Vanishing-weight or node-collision obstruction for the three-atom Hankel determinant. -/
def xiFiberPronyCollisionOrVanishing (w1 w2 w3 a1 a2 a3 : ℤ) : Prop :=
  w1 = 0 ∨ w2 = 0 ∨ w3 = 0 ∨ a1 = a2 ∨ a1 = a3 ∨ a2 = a3

/-- The `3 × 3` Hankel conductor equals the Vandermonde-square factorization; non-vanishing modulo
`p` is exactly the bad-prime exclusion criterion, and an actual determinant collapse forces the
expected Prony obstruction.
    cor:xi-fiber-spectrum-hankel-conductor-prony-padic -/
theorem paper_xi_fiber_spectrum_hankel_conductor_prony_padic
    (p : ℕ) (w1 w2 w3 a1 a2 a3 : ℤ) :
    (hankel3 w1 w2 w3 a1 a2 a3).det =
        w1 * w2 * w3 * (a2 - a1) ^ 2 * (a3 - a1) ^ 2 * (a3 - a2) ^ 2 ∧
      (xiFiberPronyPadicUnique p w1 w2 w3 a1 a2 a3 ↔
        ¬ xiFiberPronyPadicBadPrime p w1 w2 w3 a1 a2 a3) ∧
      ((hankel3 w1 w2 w3 a1 a2 a3).det = 0 →
        xiFiberPronyCollisionOrVanishing w1 w2 w3 a1 a2 a3) := by
  refine ⟨paper_xi_hankel_determinantal_radical_eq_rigidity.1 _ _ _ _ _ _, ?_, ?_⟩
  · constructor
    · intro huniq hbad
      exact huniq ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hbad)
    · intro hgood hzero
      exact hgood ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hzero)
  · intro hdet
    exact (paper_xi_hankel_determinantal_radical_eq_rigidity.2 _ _ _ _ _ _).1 hdet

end Omega.Zeta
