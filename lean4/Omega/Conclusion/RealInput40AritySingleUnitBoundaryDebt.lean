import Mathlib.Tactic

namespace Omega.Conclusion

/-- Essential real-input-40 core vertices. -/
abbrev conclusion_realinput40_arity_single_unit_boundary_debt_vertex := Fin 20

/-- Directed edges in the essential core. -/
abbrev conclusion_realinput40_arity_single_unit_boundary_debt_edge :=
  conclusion_realinput40_arity_single_unit_boundary_debt_vertex ×
    conclusion_realinput40_arity_single_unit_boundary_debt_vertex

/-- Concrete finite path ledger for the single-unit boundary-debt statement. -/
structure conclusion_realinput40_arity_single_unit_boundary_debt_data where
  conclusion_realinput40_arity_single_unit_boundary_debt_path :
    List conclusion_realinput40_arity_single_unit_boundary_debt_edge
  conclusion_realinput40_arity_single_unit_boundary_debt_source :
    conclusion_realinput40_arity_single_unit_boundary_debt_vertex
  conclusion_realinput40_arity_single_unit_boundary_debt_target :
    conclusion_realinput40_arity_single_unit_boundary_debt_vertex
  conclusion_realinput40_arity_single_unit_boundary_debt_chi :
    conclusion_realinput40_arity_single_unit_boundary_debt_edge → ℤ
  conclusion_realinput40_arity_single_unit_boundary_debt_g :
    conclusion_realinput40_arity_single_unit_boundary_debt_edge → ℤ
  conclusion_realinput40_arity_single_unit_boundary_debt_V :
    conclusion_realinput40_arity_single_unit_boundary_debt_vertex → ℤ
  conclusion_realinput40_arity_single_unit_boundary_debt_decomposition :
    (conclusion_realinput40_arity_single_unit_boundary_debt_path.map
        conclusion_realinput40_arity_single_unit_boundary_debt_chi).sum =
      (conclusion_realinput40_arity_single_unit_boundary_debt_path.map
          conclusion_realinput40_arity_single_unit_boundary_debt_g).sum +
        conclusion_realinput40_arity_single_unit_boundary_debt_V
            conclusion_realinput40_arity_single_unit_boundary_debt_source -
          conclusion_realinput40_arity_single_unit_boundary_debt_V
            conclusion_realinput40_arity_single_unit_boundary_debt_target
  conclusion_realinput40_arity_single_unit_boundary_debt_g_binary :
    ∀ e ∈ conclusion_realinput40_arity_single_unit_boundary_debt_path,
      conclusion_realinput40_arity_single_unit_boundary_debt_g e = 0 ∨
        conclusion_realinput40_arity_single_unit_boundary_debt_g e = 1
  conclusion_realinput40_arity_single_unit_boundary_debt_V_binary :
    ∀ x,
      conclusion_realinput40_arity_single_unit_boundary_debt_V x = 0 ∨
        conclusion_realinput40_arity_single_unit_boundary_debt_V x = 1

namespace conclusion_realinput40_arity_single_unit_boundary_debt_data

/-- Total path charge. -/
def conclusion_realinput40_arity_single_unit_boundary_debt_path_charge
    (D : conclusion_realinput40_arity_single_unit_boundary_debt_data) : ℤ :=
  (D.conclusion_realinput40_arity_single_unit_boundary_debt_path.map
    D.conclusion_realinput40_arity_single_unit_boundary_debt_chi).sum

/-- Bulk charge along the path. -/
def conclusion_realinput40_arity_single_unit_boundary_debt_bulk_charge
    (D : conclusion_realinput40_arity_single_unit_boundary_debt_data) : ℤ :=
  (D.conclusion_realinput40_arity_single_unit_boundary_debt_path.map
    D.conclusion_realinput40_arity_single_unit_boundary_debt_g).sum

end conclusion_realinput40_arity_single_unit_boundary_debt_data

open conclusion_realinput40_arity_single_unit_boundary_debt_data

lemma conclusion_realinput40_arity_single_unit_boundary_debt_bulk_charge_nonneg
    (path : List conclusion_realinput40_arity_single_unit_boundary_debt_edge)
    (g : conclusion_realinput40_arity_single_unit_boundary_debt_edge → ℤ)
    (hg : ∀ e ∈ path, g e = 0 ∨ g e = 1) :
    0 ≤ (path.map g).sum := by
  induction path with
  | nil => simp
  | cons e rest ih =>
      have he : 0 ≤ g e := by
        rcases hg e (by simp) with he0 | he1
        · simp [he0]
        · simp [he1]
      have hrest : ∀ x ∈ rest, g x = 0 ∨ g x = 1 := by
        intro x hx
        exact hg x (by simp [hx])
      have ihrest : 0 ≤ (rest.map g).sum := ih hrest
      simp only [List.map_cons, List.sum_cons]
      linarith

/-- Concrete statement: every finite path has charge at least `-1`, and closed paths have
nonnegative charge because the endpoint potential cancels. -/
def conclusion_realinput40_arity_single_unit_boundary_debt_statement
    (D : conclusion_realinput40_arity_single_unit_boundary_debt_data) : Prop :=
  -1 ≤ D.conclusion_realinput40_arity_single_unit_boundary_debt_path_charge ∧
    (D.conclusion_realinput40_arity_single_unit_boundary_debt_source =
        D.conclusion_realinput40_arity_single_unit_boundary_debt_target →
      0 ≤ D.conclusion_realinput40_arity_single_unit_boundary_debt_path_charge) ∧
    D.conclusion_realinput40_arity_single_unit_boundary_debt_path_charge =
      D.conclusion_realinput40_arity_single_unit_boundary_debt_bulk_charge +
        D.conclusion_realinput40_arity_single_unit_boundary_debt_V
            D.conclusion_realinput40_arity_single_unit_boundary_debt_source -
          D.conclusion_realinput40_arity_single_unit_boundary_debt_V
            D.conclusion_realinput40_arity_single_unit_boundary_debt_target

/-- Paper label: `thm:conclusion-realinput40-arity-single-unit-boundary-debt`. -/
theorem paper_conclusion_realinput40_arity_single_unit_boundary_debt
    (D : conclusion_realinput40_arity_single_unit_boundary_debt_data) :
    conclusion_realinput40_arity_single_unit_boundary_debt_statement D := by
  have hbulk : 0 ≤ D.conclusion_realinput40_arity_single_unit_boundary_debt_bulk_charge :=
    conclusion_realinput40_arity_single_unit_boundary_debt_bulk_charge_nonneg
      D.conclusion_realinput40_arity_single_unit_boundary_debt_path
      D.conclusion_realinput40_arity_single_unit_boundary_debt_g
      D.conclusion_realinput40_arity_single_unit_boundary_debt_g_binary
  have hsource := D.conclusion_realinput40_arity_single_unit_boundary_debt_V_binary
    D.conclusion_realinput40_arity_single_unit_boundary_debt_source
  have htarget := D.conclusion_realinput40_arity_single_unit_boundary_debt_V_binary
    D.conclusion_realinput40_arity_single_unit_boundary_debt_target
  have hboundary :
      -1 ≤
        D.conclusion_realinput40_arity_single_unit_boundary_debt_V
            D.conclusion_realinput40_arity_single_unit_boundary_debt_source -
          D.conclusion_realinput40_arity_single_unit_boundary_debt_V
            D.conclusion_realinput40_arity_single_unit_boundary_debt_target := by
    rcases hsource with hs | hs <;> rcases htarget with ht | ht <;> simp [hs, ht]
  have hdecomp :
      D.conclusion_realinput40_arity_single_unit_boundary_debt_path_charge =
        D.conclusion_realinput40_arity_single_unit_boundary_debt_bulk_charge +
          D.conclusion_realinput40_arity_single_unit_boundary_debt_V
              D.conclusion_realinput40_arity_single_unit_boundary_debt_source -
            D.conclusion_realinput40_arity_single_unit_boundary_debt_V
              D.conclusion_realinput40_arity_single_unit_boundary_debt_target := by
    simpa [conclusion_realinput40_arity_single_unit_boundary_debt_path_charge,
      conclusion_realinput40_arity_single_unit_boundary_debt_bulk_charge] using
      D.conclusion_realinput40_arity_single_unit_boundary_debt_decomposition
  refine ⟨?_, ?_, hdecomp⟩
  · rw [hdecomp]
    linarith
  · intro hclosed
    rw [hdecomp, hclosed]
    linarith

end Omega.Conclusion
