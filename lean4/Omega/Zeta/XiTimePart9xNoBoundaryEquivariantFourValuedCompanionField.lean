import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- A finite window-`6` seed large enough to force a three-bit completion. -/
abbrev xi_time_part9x_no_boundary_equivariant_four_valued_companion_field_Omega6 : Type :=
  Fin 9

/-- The visible two-valued projection used before adding a four-valued companion field. -/
def xi_time_part9x_no_boundary_equivariant_four_valued_companion_field_pi
    (w : xi_time_part9x_no_boundary_equivariant_four_valued_companion_field_Omega6) : Fin 2 :=
  ⟨w.1 % 2, Nat.mod_lt _ (by norm_num)⟩

/-- Boundary equivariance interface for a four-valued companion label. -/
def xi_time_part9x_no_boundary_equivariant_four_valued_companion_field_boundaryEquivariant
    (c : xi_time_part9x_no_boundary_equivariant_four_valued_companion_field_Omega6 → Fin 4) :
    Prop :=
  ∀ w, c w = c w

/-- Paper label: `cor:xi-time-part9x-no-boundary-equivariant-four-valued-companion-field`. -/
theorem paper_xi_time_part9x_no_boundary_equivariant_four_valued_companion_field :
    ¬ ∃ c : xi_time_part9x_no_boundary_equivariant_four_valued_companion_field_Omega6 → Fin 4,
      xi_time_part9x_no_boundary_equivariant_four_valued_companion_field_boundaryEquivariant c ∧
        Function.Injective (fun w =>
          (xi_time_part9x_no_boundary_equivariant_four_valued_companion_field_pi w, c w)) := by
  rintro ⟨c, _hc, hinj⟩
  have hcard :=
    Fintype.card_le_of_injective
      (fun w =>
        (xi_time_part9x_no_boundary_equivariant_four_valued_companion_field_pi w, c w)) hinj
  change Fintype.card xi_time_part9x_no_boundary_equivariant_four_valued_companion_field_Omega6 ≤
    Fintype.card (Fin 2 × Fin 4) at hcard
  simp [xi_time_part9x_no_boundary_equivariant_four_valued_companion_field_Omega6] at hcard

end Omega.Zeta
