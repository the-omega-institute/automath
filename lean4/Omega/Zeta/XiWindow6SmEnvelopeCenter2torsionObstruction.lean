import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite two-torsion bookkeeping for a Standard-Model-envelope center quotient.
The center `2`-torsion maps to a finite quotient with at most two `2`-torsion classes, and
each quotient fiber is bounded by the one-dimensional torus `2`-torsion. -/
structure xi_window6_sm_envelope_center_2torsion_obstruction_Data where
  xi_window6_sm_envelope_center_2torsion_obstruction_centerTwoTorsion : Type
  xi_window6_sm_envelope_center_2torsion_obstruction_centerFintype :
    Fintype xi_window6_sm_envelope_center_2torsion_obstruction_centerTwoTorsion
  xi_window6_sm_envelope_center_2torsion_obstruction_quotientTwoTorsion : Type
  xi_window6_sm_envelope_center_2torsion_obstruction_quotientFintype :
    Fintype xi_window6_sm_envelope_center_2torsion_obstruction_quotientTwoTorsion
  xi_window6_sm_envelope_center_2torsion_obstruction_centerToQuotient :
    xi_window6_sm_envelope_center_2torsion_obstruction_centerTwoTorsion →
      xi_window6_sm_envelope_center_2torsion_obstruction_quotientTwoTorsion
  xi_window6_sm_envelope_center_2torsion_obstruction_torusTwoTorsionCard : ℕ
  xi_window6_sm_envelope_center_2torsion_obstruction_center_card_le_fiber_product :
    Fintype.card xi_window6_sm_envelope_center_2torsion_obstruction_centerTwoTorsion ≤
      Fintype.card xi_window6_sm_envelope_center_2torsion_obstruction_quotientTwoTorsion *
        xi_window6_sm_envelope_center_2torsion_obstruction_torusTwoTorsionCard
  xi_window6_sm_envelope_center_2torsion_obstruction_quotient_card_le :
    Fintype.card xi_window6_sm_envelope_center_2torsion_obstruction_quotientTwoTorsion ≤ 2
  xi_window6_sm_envelope_center_2torsion_obstruction_torus_card_le :
    xi_window6_sm_envelope_center_2torsion_obstruction_torusTwoTorsionCard ≤ 2

namespace xi_window6_sm_envelope_center_2torsion_obstruction_Data

/-- The paper-facing obstruction: the center has at most four two-torsion points, hence no
injective copy of the three-axis Boolean register. -/
def Holds (D : xi_window6_sm_envelope_center_2torsion_obstruction_Data) : Prop :=
  letI := D.xi_window6_sm_envelope_center_2torsion_obstruction_centerFintype
  Fintype.card D.xi_window6_sm_envelope_center_2torsion_obstruction_centerTwoTorsion ≤ 4 ∧
    ¬ ∃ f : (Fin 3 → ZMod 2) →
        D.xi_window6_sm_envelope_center_2torsion_obstruction_centerTwoTorsion,
      Function.Injective f

end xi_window6_sm_envelope_center_2torsion_obstruction_Data

/-- Paper label: `thm:xi-window6-sm-envelope-center-2torsion-obstruction`. -/
theorem paper_xi_window6_sm_envelope_center_2torsion_obstruction
    (D : xi_window6_sm_envelope_center_2torsion_obstruction_Data) : D.Holds := by
  letI := D.xi_window6_sm_envelope_center_2torsion_obstruction_centerFintype
  letI := D.xi_window6_sm_envelope_center_2torsion_obstruction_quotientFintype
  have hcenter :
      Fintype.card D.xi_window6_sm_envelope_center_2torsion_obstruction_centerTwoTorsion ≤
        4 := by
    calc
      Fintype.card D.xi_window6_sm_envelope_center_2torsion_obstruction_centerTwoTorsion ≤
          Fintype.card
              D.xi_window6_sm_envelope_center_2torsion_obstruction_quotientTwoTorsion *
            D.xi_window6_sm_envelope_center_2torsion_obstruction_torusTwoTorsionCard :=
        D.xi_window6_sm_envelope_center_2torsion_obstruction_center_card_le_fiber_product
      _ ≤ 2 * 2 := by
        exact Nat.mul_le_mul
          D.xi_window6_sm_envelope_center_2torsion_obstruction_quotient_card_le
          D.xi_window6_sm_envelope_center_2torsion_obstruction_torus_card_le
      _ = 4 := by norm_num
  refine ⟨hcenter, ?_⟩
  rintro ⟨f, hf⟩
  have hcard :
      Fintype.card (Fin 3 → ZMod 2) ≤
        Fintype.card
          D.xi_window6_sm_envelope_center_2torsion_obstruction_centerTwoTorsion :=
    Fintype.card_le_of_injective f hf
  have hdomain : Fintype.card (Fin 3 → ZMod 2) = 8 := by
    simp
  omega

end Omega.Zeta
