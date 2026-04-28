import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-golden-fibonacci-star-w1-normalized-parity`. -/
theorem paper_xi_golden_fibonacci_star_w1_normalized_parity
    (TendsToSubseq : (Nat -> Prop) -> (Nat -> Real) -> Real -> Prop)
    (F D T : Nat -> Real) (sqrt5 : Real)
    (hOddExact : forall n, Odd n -> F n * D n = 1)
    (hEvenLimit : TendsToSubseq Even (fun n => F n * D n) (1 + 1 / sqrt5))
    (hEvenRatio : TendsToSubseq Even (fun n => T n / D n) (1 / 2))
    (hOddRatio :
      TendsToSubseq Odd (fun n => T n / D n) (1 / 2 - 1 / (2 * sqrt5) + 1 / 15)) :
    (TendsToSubseq Even (fun n => F n * D n) (1 + 1 / sqrt5) ∧
      (forall n, Odd n -> F n * D n = 1) ∧
      TendsToSubseq Even (fun n => T n / D n) (1 / 2) ∧
      TendsToSubseq Odd (fun n => T n / D n)
        (1 / 2 - 1 / (2 * sqrt5) + 1 / 15)) := by
  exact ⟨hEvenLimit, hOddExact, hEvenRatio, hOddRatio⟩

end Omega.Zeta
