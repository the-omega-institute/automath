import Mathlib.Tactic
import Omega.Folding.BinFold
import Omega.Folding.StableSyntax
import Omega.Combinatorics.FibonacciCube

namespace Omega.Zeta

/-- The concrete window-`6` minimal multiplicity sector. -/
abbrev xi_time_part9xab_window6_minsector_rigid_x4_subcover_minSector :=
  {w : Omega.X 6 // Omega.cBinFiberMult 6 w = 2}

private theorem xi_time_part9xab_window6_minsector_rigid_x4_subcover_card_minSector :
    Fintype.card xi_time_part9xab_window6_minsector_rigid_x4_subcover_minSector = 8 := by
  classical
  rw [Fintype.card_subtype]
  change (Finset.univ.filter (fun x : Omega.X 6 => Omega.cBinFiberMult 6 x = 2)).card = 8
  rw [show (Finset.univ : Finset (Omega.X 6)) =
      (@Finset.univ (Omega.X 6) (Omega.fintypeX 6)) by ext x; simp]
  exact Omega.cBinFiberHist_6_2

private noncomputable def xi_time_part9xab_window6_minsector_rigid_x4_subcover_equiv :
    Omega.X 4 ≃ xi_time_part9xab_window6_minsector_rigid_x4_subcover_minSector :=
  Fintype.equivOfCardEq (by
    rw [Omega.X.card_eq_fib,
      xi_time_part9xab_window6_minsector_rigid_x4_subcover_card_minSector]
    norm_num)

/-- A cardinality-rigid embedding of `X 4` onto the window-`6` multiplicity-`2` sector. -/
noncomputable def xi_time_part9xab_window6_minsector_rigid_x4_subcover_iota4
    (v : Omega.X 4) : Omega.X 6 :=
  (xi_time_part9xab_window6_minsector_rigid_x4_subcover_equiv v).1

/-- Paper label: `thm:xi-time-part9xab-window6-minsector-rigid-x4-subcover`. -/
theorem paper_xi_time_part9xab_window6_minsector_rigid_x4_subcover :
    {w : Omega.X 6 | Omega.cBinFiberMult 6 w = 2} =
      Set.range xi_time_part9xab_window6_minsector_rigid_x4_subcover_iota4 := by
  ext w
  constructor
  · intro hw
    obtain ⟨v, hv⟩ :=
      xi_time_part9xab_window6_minsector_rigid_x4_subcover_equiv.surjective ⟨w, hw⟩
    refine ⟨v, ?_⟩
    exact congrArg Subtype.val hv
  · rintro ⟨v, rfl⟩
    exact (xi_time_part9xab_window6_minsector_rigid_x4_subcover_equiv v).2

end Omega.Zeta
