import Omega.Kronecker.W1DenominatorClosedForm
import Mathlib.Tactic

namespace Omega.Kronecker

/-- Paper label: `cor:kronecker-w1-two-sided-interpretation`.
Repackaging the denominator closed form into the paper's two-sided interpretation:
on the bad side the transport equals half the corresponding star-discrepancy budget,
while on the good side the quadratic closed form records the intra-box sensitivity. -/
theorem paper_kronecker_w1_two_sided_interpretation (p q : Nat) (hq : 0 < q) (alpha : Rat) :
    let delta := alpha - (p : Rat) / q
    (delta < 0 ->
      2 * kroneckerBadSideW1 q delta =
        (1 : Rat) / q + ((q - 1 : Nat) : Rat) * (((p : Rat) / q) - alpha)) /\
    (0 < delta ->
      kroneckerGoodSideW1 q delta =
        (1 : Rat) / (2 * q) - ((q - 1 : Nat) : Rat) / 2 * delta +
          ((q * (q - 1) * (2 * q - 1) : Nat) : Rat) / 6 * delta ^ 2) := by
  dsimp
  have hclosed := paper_kronecker_w1_denominator_closed_form p q hq alpha
  constructor
  · intro hdelta
    unfold kroneckerBadSideW1
    ring
  · intro hdelta
    exact (hclosed.1 hdelta)

end Omega.Kronecker
