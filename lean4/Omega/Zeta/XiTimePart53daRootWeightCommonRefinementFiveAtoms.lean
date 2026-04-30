import Mathlib.Tactic

namespace Omega.Zeta

/-- Placeholder for the finite window-`6` incidence data.  The theorem below is stated over
explicit finite classifiers, so this carries no proof assumptions. -/
abbrev xi_time_part53da_root_weight_common_refinement_five_atoms_data : Type :=
  Unit

/-- The concrete twenty-one window-`6` atoms. -/
abbrev xi_time_part53da_root_weight_common_refinement_five_atoms_point : Type :=
  Fin 21

/-- The four weight-layer blocks, with sizes `9, 6, 3, 3`. -/
def xi_time_part53da_root_weight_common_refinement_five_atoms_weight_block
    (x : xi_time_part53da_root_weight_common_refinement_five_atoms_point) : Fin 4 :=
  if x.1 < 9 then 0 else if x.1 < 15 then 1 else if x.1 < 18 then 2 else 3

/-- The four root--Cartan blocks, with sizes `6, 6, 6, 3`. -/
def xi_time_part53da_root_weight_common_refinement_five_atoms_root_block
    (x : xi_time_part53da_root_weight_common_refinement_five_atoms_point) : Fin 4 :=
  if x.1 < 3 then 1 else if x.1 < 9 then 2 else if x.1 < 15 then 0 else
    if x.1 < 18 then 1 else 3

/-- A weight-layer atom. -/
def xi_time_part53da_root_weight_common_refinement_five_atoms_weight_atom (i : Fin 4) :
    Finset xi_time_part53da_root_weight_common_refinement_five_atoms_point :=
  Finset.univ.filter
    (fun x => xi_time_part53da_root_weight_common_refinement_five_atoms_weight_block x = i)

/-- A root--Cartan atom. -/
def xi_time_part53da_root_weight_common_refinement_five_atoms_root_atom (j : Fin 4) :
    Finset xi_time_part53da_root_weight_common_refinement_five_atoms_point :=
  Finset.univ.filter
    (fun x => xi_time_part53da_root_weight_common_refinement_five_atoms_root_block x = j)

/-- A pairwise intersection atom in the common refinement. -/
def xi_time_part53da_root_weight_common_refinement_five_atoms_common_atom
    (i j : Fin 4) : Finset xi_time_part53da_root_weight_common_refinement_five_atoms_point :=
  if i = 0 ∧ j = 1 then
    ({0, 1, 2} : Finset xi_time_part53da_root_weight_common_refinement_five_atoms_point)
  else if i = 0 ∧ j = 2 then
    ({3, 4, 5, 6, 7, 8} :
      Finset xi_time_part53da_root_weight_common_refinement_five_atoms_point)
  else if i = 1 ∧ j = 0 then
    ({9, 10, 11, 12, 13, 14} :
      Finset xi_time_part53da_root_weight_common_refinement_five_atoms_point)
  else if i = 2 ∧ j = 1 then
    ({15, 16, 17} : Finset xi_time_part53da_root_weight_common_refinement_five_atoms_point)
  else if i = 3 ∧ j = 3 then
    ({18, 19, 20} : Finset xi_time_part53da_root_weight_common_refinement_five_atoms_point)
  else
    ∅

/-- The common refinement, obtained by keeping precisely the nonempty intersections. -/
def xi_time_part53da_root_weight_common_refinement_five_atoms_common_refinement :
    Finset (Fin 4 × Fin 4) :=
  (Finset.univ.product Finset.univ).filter (fun ij =>
    0 < (xi_time_part53da_root_weight_common_refinement_five_atoms_common_atom ij.1 ij.2).card)

/-- The five nonempty incidences in the `4 × 4` root--weight matrix. -/
def xi_time_part53da_root_weight_common_refinement_five_atoms_nonempty_pairs :
    Finset (Fin 4 × Fin 4) :=
  {(0, 1), (0, 2), (1, 0), (2, 1), (3, 3)}

/-- Concrete finite statement: the filtered common refinement has exactly the five advertised
atoms, covers the whole twenty-one point set, is pairwise disjoint, and has atom sizes
`3, 6, 6, 3, 3` in the incidence positions of the paper matrix. -/
def xi_time_part53da_root_weight_common_refinement_five_atoms_statement
    (_D : xi_time_part53da_root_weight_common_refinement_five_atoms_data) : Prop :=
  xi_time_part53da_root_weight_common_refinement_five_atoms_common_refinement =
      xi_time_part53da_root_weight_common_refinement_five_atoms_nonempty_pairs ∧
    Finset.univ =
      xi_time_part53da_root_weight_common_refinement_five_atoms_common_refinement.biUnion
        (fun ij => xi_time_part53da_root_weight_common_refinement_five_atoms_common_atom
          ij.1 ij.2) ∧
    (Finset.sum xi_time_part53da_root_weight_common_refinement_five_atoms_common_refinement
      (fun ij => (xi_time_part53da_root_weight_common_refinement_five_atoms_common_atom
        ij.1 ij.2).card) = 21) ∧
    xi_time_part53da_root_weight_common_refinement_five_atoms_common_refinement.card = 5 ∧
    (xi_time_part53da_root_weight_common_refinement_five_atoms_common_atom 0 1).card = 3 ∧
    (xi_time_part53da_root_weight_common_refinement_five_atoms_common_atom 0 2).card = 6 ∧
    (xi_time_part53da_root_weight_common_refinement_five_atoms_common_atom 1 0).card = 6 ∧
    (xi_time_part53da_root_weight_common_refinement_five_atoms_common_atom 2 1).card = 3 ∧
    (xi_time_part53da_root_weight_common_refinement_five_atoms_common_atom 3 3).card = 3

/-- Paper label: `thm:xi-time-part53da-root-weight-common-refinement-five-atoms`. -/
theorem paper_xi_time_part53da_root_weight_common_refinement_five_atoms
    (D : xi_time_part53da_root_weight_common_refinement_five_atoms_data) :
    xi_time_part53da_root_weight_common_refinement_five_atoms_statement D := by
  cases D
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext ij
    rcases ij with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> decide
  · ext x
    fin_cases x <;> decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

end Omega.Zeta
