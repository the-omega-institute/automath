import Omega.Folding.MomentRecurrence

namespace Omega

/-- Paper label: `prop:pom-moment-congruence-q`. -/
theorem paper_pom_moment_congruence_q (q m : Nat) :
    momentSum q m = ∑ r ∈ Finset.range (Nat.fib (m + 2)), weightCongruenceCount m r ^ q := by
  exact momentSum_eq_congr_pow_sum q m

end Omega
