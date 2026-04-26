import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part9zbk-presingular-one-sided-approximation`. The real-axis and
imaginary-axis strict one-sided estimates are packaged as the stated two-part conclusion. -/
theorem paper_xi_time_part9zbk_presingular_one_sided_approximation
    (E En Eim Enim : Real -> Real) (phi : Real)
    (hreal : forall xi, xi != 0 -> 0 < En xi /\ En xi < E xi)
    (himag : forall tau,
      |tau| < 2 * Real.pi / phi -> 0 < Enim tau /\ Enim tau < Eim tau) :
    (forall xi, xi != 0 -> 0 < En xi /\ En xi < E xi) /\
      (forall tau, |tau| < 2 * Real.pi / phi -> 0 < Enim tau /\ Enim tau < Eim tau) := by
  exact ⟨hreal, himag⟩

end Omega.Zeta
