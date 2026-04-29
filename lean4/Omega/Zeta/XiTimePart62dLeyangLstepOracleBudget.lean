import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part62d-leyang-lstep-oracle-budget`.  Exact recovery over each
fiber makes the code injective on that fiber; a regular `4 ^ ell` fiber therefore fits into the
`2 ^ m` code space only when `2 * ell ≤ m`. -/
theorem paper_xi_time_part62d_leyang_lstep_oracle_budget {PiN PiNL Code : Type}
    [Fintype PiNL] [Fintype Code] [DecidableEq PiN] (x0 : PiN) (q : PiNL → PiN)
    (c : PiNL → Code) (D : PiN → Code → PiNL) (ell m : ℕ)
    (hCode : Fintype.card Code = 2 ^ m)
    (hFiber : ∀ x : PiN, Fintype.card {y : PiNL // q y = x} = 4 ^ ell)
    (hRecover : ∀ y : PiNL, D (q y) (c y) = y) : 2 * ell ≤ m := by
  let codeOnFiber : {y : PiNL // q y = x0} → Code := fun y => c y.1
  have hInjective : Function.Injective codeOnFiber := by
    intro a b hab
    apply Subtype.ext
    have hcodeEq : c a.1 = c b.1 := by
      simpa [codeOnFiber] using hab
    have hval : a.1 = b.1 := by
      calc
        a.1 = D x0 (c a.1) := by simpa [a.2] using (hRecover a.1).symm
        _ = D x0 (c b.1) := by rw [hcodeEq]
        _ = b.1 := by simpa [b.2] using hRecover b.1
    exact hval
  have hCard :
      Fintype.card {y : PiNL // q y = x0} ≤ Fintype.card Code :=
    Fintype.card_le_of_injective codeOnFiber hInjective
  have hBound : 4 ^ ell ≤ 2 ^ m := by
    simpa [hFiber x0, hCode] using hCard
  have hPow : 2 ^ (2 * ell) ≤ 2 ^ m := by
    have hRewrite : 4 ^ ell = 2 ^ (2 * ell) := by
      calc
        4 ^ ell = (2 ^ 2) ^ ell := by norm_num
        _ = 2 ^ (2 * ell) := by rw [pow_mul]
    simpa [hRewrite] using hBound
  exact (Nat.pow_le_pow_iff_right (show 1 < 2 by decide)).1 hPow

end Omega.Zeta
