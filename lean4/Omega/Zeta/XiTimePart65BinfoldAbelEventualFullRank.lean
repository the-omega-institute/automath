import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Zeta.XiTimePart65BinfoldGaugeCenterAbelianizationExact

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part65-binfold-abel-eventual-full-rank`. -/
theorem paper_xi_time_part65_binfold_abel_eventual_full_rank
    (fiber : (m : Nat) → Fin (Nat.fib (m + 2)) → Nat)
    (hEventual : ∃ m0, ∀ m, m0 ≤ m → ∀ w, 2 ≤ fiber m w) :
    ∃ m0, ∀ m, m0 ≤ m →
      Omega.OperatorAlgebra.foldGaugeAbelianizationOrder (fiber m) = 2 ^ Nat.fib (m + 2) := by
  rcases hEventual with ⟨m0, hm0⟩
  refine ⟨m0, ?_⟩
  intro m hm
  have hexact :=
    (paper_xi_time_part65_binfold_gauge_center_abelianization_exact (fiber m)).2
  have hfilter :
      (Finset.univ.filter fun w : Fin (Nat.fib (m + 2)) => 2 ≤ fiber m w) =
        Finset.univ := by
    apply Finset.filter_true_of_mem
    intro w _hw
    exact hm0 m hm w
  rw [hfilter] at hexact
  simpa using hexact

end Omega.Zeta
