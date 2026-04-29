import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The three boundary axes in the lifted window-`6` boundary sector. -/
abbrev xi_time_part53da_boundary_z6_torsor_axis : Type :=
  ZMod 3

/-- The two sheet choices over each boundary axis. -/
abbrev xi_time_part53da_boundary_z6_torsor_sheet : Type :=
  ZMod 2

/-- The six lifted boundary points: a three-cycle axis and a two-sheet coordinate. -/
abbrev xi_time_part53da_boundary_z6_torsor_point : Type :=
  xi_time_part53da_boundary_z6_torsor_axis × xi_time_part53da_boundary_z6_torsor_sheet

/-- The commuting product action: rotate the boundary axis and flip the sheet. -/
def xi_time_part53da_boundary_z6_torsor_action
    (g : ZMod 3 × ZMod 2) (x : xi_time_part53da_boundary_z6_torsor_point) :
    xi_time_part53da_boundary_z6_torsor_point :=
  (g.1 + x.1, g.2 + x.2)

/-- Concrete regularity statement for the six lifted boundary points. -/
def xi_time_part53da_boundary_z6_torsor_statement : Prop :=
  Fintype.card xi_time_part53da_boundary_z6_torsor_point = 6 ∧
    Fintype.card (ZMod 3 × ZMod 2) = 6 ∧
    Nonempty ((ZMod 3 × ZMod 2) ≃ ZMod 6) ∧
    ∀ x y : xi_time_part53da_boundary_z6_torsor_point,
      ∃! g : ZMod 3 × ZMod 2, xi_time_part53da_boundary_z6_torsor_action g x = y

/-- Paper label: `thm:xi-time-part53da-boundary-z6-torsor`. -/
theorem paper_xi_time_part53da_boundary_z6_torsor :
    xi_time_part53da_boundary_z6_torsor_statement := by
  refine ⟨by
    change Fintype.card (ZMod 3 × ZMod 2) = 6
    norm_num [Fintype.card_prod], by
    change Fintype.card (ZMod 3 × ZMod 2) = 6
    norm_num [Fintype.card_prod], ?_, ?_⟩
  · exact ⟨Fintype.equivOfCardEq (α := ZMod 3 × ZMod 2) (β := ZMod 6)
      (by norm_num [Fintype.card_prod])⟩
  · intro x y
    refine ⟨(y.1 - x.1, y.2 - x.2), ?_, ?_⟩
    · ext <;> simp [xi_time_part53da_boundary_z6_torsor_action]
    · intro g hg
      ext
      · have h := congrArg Prod.fst hg
        have h' : g.1 + x.1 = y.1 := by
          simpa [xi_time_part53da_boundary_z6_torsor_action] using h
        calc
          g.1 = g.1 + x.1 - x.1 := by abel
          _ = y.1 - x.1 := by rw [h']
      · have h := congrArg Prod.snd hg
        have h' : g.2 + x.2 = y.2 := by
          simpa [xi_time_part53da_boundary_z6_torsor_action] using h
        calc
          g.2 = g.2 + x.2 - x.2 := by abel
          _ = y.2 - x.2 := by rw [h']

end Omega.Zeta
