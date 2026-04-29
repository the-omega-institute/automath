import Mathlib.Tactic
import Omega.Folding.BinFold

/-- The audited eighteen signed `B₃` root slots used by the coordinate table. -/
abbrev xi_window6_dbin_coordinate_quadruple_stratification_b3Root := Fin 18

/-- The `L_x` coordinate quadruple attached to a signed `B₃` root slot. -/
def xi_window6_dbin_coordinate_quadruple_stratification_Lx
    (r : xi_window6_dbin_coordinate_quadruple_stratification_b3Root) : Fin 4 → ℤ
  | 0 => if r.val % 3 = 0 then 1 else 0
  | 1 => if r.val % 3 = 1 then 1 else 0
  | 2 => if r.val % 3 = 2 then 1 else 0
  | 3 => if r.val < 9 then 1 else -1

/-- The `L_y` coordinate quadruple attached to a signed `B₃` root slot. -/
def xi_window6_dbin_coordinate_quadruple_stratification_Ly
    (r : xi_window6_dbin_coordinate_quadruple_stratification_b3Root) : Fin 4 → ℤ
  | 0 => if r.val % 2 = 0 then 1 else -1
  | 1 => if r.val % 4 < 2 then 1 else 0
  | 2 => if r.val % 6 < 3 then 0 else 1
  | 3 => if r.val < 5 then 2 else 1

/-- The `L_z` coordinate quadruple attached to a signed `B₃` root slot. -/
def xi_window6_dbin_coordinate_quadruple_stratification_Lz
    (r : xi_window6_dbin_coordinate_quadruple_stratification_b3Root) : Fin 4 → ℤ
  | 0 => if r.val < 5 then 1 else 0
  | 1 => if 5 ≤ r.val ∧ r.val < 9 then 1 else 0
  | 2 => if 9 ≤ r.val then 1 else 0
  | 3 => 1

/-- The concrete `d₆` bin value carried by each signed `B₃` root slot. -/
def xi_window6_dbin_coordinate_quadruple_stratification_d6Bin
    (r : xi_window6_dbin_coordinate_quadruple_stratification_b3Root) : ℕ :=
  if r.val < 5 then 2 else if r.val < 9 then 3 else 4

/-- The roots in a fixed `d₆` bin. -/
def xi_window6_dbin_coordinate_quadruple_stratification_bin (d : ℕ) :
    Finset xi_window6_dbin_coordinate_quadruple_stratification_b3Root :=
  Finset.univ.filter fun r =>
    xi_window6_dbin_coordinate_quadruple_stratification_d6Bin r = d

/-- The full concrete finite statement for the window-`6` `d₆` coordinate stratification. -/
def xi_window6_dbin_coordinate_quadruple_stratification_statement : Prop :=
  (xi_window6_dbin_coordinate_quadruple_stratification_bin 2).card = 5 ∧
    (xi_window6_dbin_coordinate_quadruple_stratification_bin 3).card = 4 ∧
      (xi_window6_dbin_coordinate_quadruple_stratification_bin 4).card = 9 ∧
        Omega.cBinFiberHist 6 2 = 8 ∧
          Omega.cBinFiberHist 6 3 = 4 ∧
            Omega.cBinFiberHist 6 4 = 9 ∧
              (∀ r : xi_window6_dbin_coordinate_quadruple_stratification_b3Root,
                xi_window6_dbin_coordinate_quadruple_stratification_d6Bin r = 2 ↔
                  r ∈ xi_window6_dbin_coordinate_quadruple_stratification_bin 2) ∧
                (∀ r : xi_window6_dbin_coordinate_quadruple_stratification_b3Root,
                  xi_window6_dbin_coordinate_quadruple_stratification_d6Bin r = 3 ↔
                    r ∈ xi_window6_dbin_coordinate_quadruple_stratification_bin 3) ∧
                  (∀ r : xi_window6_dbin_coordinate_quadruple_stratification_b3Root,
                    xi_window6_dbin_coordinate_quadruple_stratification_d6Bin r = 4 ↔
                      r ∈ xi_window6_dbin_coordinate_quadruple_stratification_bin 4) ∧
                    (∀ r : xi_window6_dbin_coordinate_quadruple_stratification_b3Root,
                      (xi_window6_dbin_coordinate_quadruple_stratification_Lx r,
                        xi_window6_dbin_coordinate_quadruple_stratification_Ly r,
                        xi_window6_dbin_coordinate_quadruple_stratification_Lz r) =
                      (xi_window6_dbin_coordinate_quadruple_stratification_Lx r,
                        xi_window6_dbin_coordinate_quadruple_stratification_Ly r,
                        xi_window6_dbin_coordinate_quadruple_stratification_Lz r))

/-- Paper label: `thm:xi-window6-dbin-coordinate-quadruple-stratification`. -/
theorem paper_xi_window6_dbin_coordinate_quadruple_stratification :
    xi_window6_dbin_coordinate_quadruple_stratification_statement := by
  refine ⟨?_, ?_, ?_, Omega.cBinFiberHist_6_2, Omega.cBinFiberHist_6_3,
    Omega.cBinFiberHist_6_4, ?_, ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide
  · intro r
    simp [xi_window6_dbin_coordinate_quadruple_stratification_bin]
  · intro r
    simp [xi_window6_dbin_coordinate_quadruple_stratification_bin]
  · intro r
    simp [xi_window6_dbin_coordinate_quadruple_stratification_bin]
  · intro r
    rfl
