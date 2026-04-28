import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.LeyangLissajousImmersionCriterion

namespace Omega.Zeta

/-- Paper label:
`prop:xi-time-part62da-lissajous-two-nonimmersed-points`. In the coprime case the
gcd-controlled phase lattice in the Lissajous immersion criterion is the single
`π / b` lattice. -/
theorem paper_xi_time_part62da_lissajous_two_nonimmersed_points
    (a b : Nat) (delta : Real) (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b) :
    ((Exists fun t : Real =>
      -(a : Real) * Real.sin ((a : Real) * t + delta) = 0 ∧
        -(b : Real) * Real.sin ((b : Real) * t) = 0) ↔
      Exists fun k : Int => delta = ((k : Real) * Real.pi) / (b : Real)) := by
  have hcrit :=
    Omega.UnitCirclePhaseArithmetic.paper_leyang_lissajous_immersion_criterion
      a b delta ha hb
  have hgcd : Nat.gcd a b = 1 := hcop.gcd_eq_one
  constructor
  · intro h
    rcases hcrit.mp h with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    simpa [hgcd] using hk
  · rintro ⟨k, hk⟩
    apply hcrit.mpr
    refine ⟨k, ?_⟩
    simpa [hgcd] using hk

end Omega.Zeta
