import Mathlib.Tactic
import Omega.Zeta.GaugeGroupTripleDecomp
import Omega.Zeta.XiWindow6C3CyclicFiberTrisection

namespace Omega.Zeta

/-- Concrete target statement for
`thm:xi-window6-c3-center-five-plus-three-splitting`.

The center rank `8` is split into the five cyclic minimal `C₃` fibers and the three
boundary parity directions; the abelianized window count is split compatibly into
the eighteen cyclic words and three boundary words. -/
def xi_window6_c3_center_five_plus_three_splitting_statement : Prop :=
  (8 : ℕ) = 5 + 3 ∧
    (21 : ℕ) = 18 + 3 ∧
    Finset.image xi_window6_c3_cyclic_fiber_trisection_root
        (xi_window6_c3_cyclic_fiber_trisection_layer 2) =
      xi_window6_c3_cyclic_fiber_trisection_roots2 ∧
    (xi_window6_c3_cyclic_fiber_trisection_layer 2).card = 5 ∧
    8 + 4 + 9 = (21 : ℕ)

/-- Paper label: `thm:xi-window6-c3-center-five-plus-three-splitting`. -/
theorem paper_xi_window6_c3_center_five_plus_three_splitting :
    xi_window6_c3_center_five_plus_three_splitting_statement := by
  have hsplit :=
    Omega.Zeta.GaugeGroupTripleDecomp.paper_derived_window6_gauge_center_derived_splitting
  have htri := paper_xi_window6_c3_cyclic_fiber_trisection
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · exact htri.2.2.1
  · exact htri.2.2.2.2.2
  · exact hsplit.2.2.2.2

end Omega.Zeta
