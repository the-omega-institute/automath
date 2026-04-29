import Mathlib.Tactic

theorem paper_pom_nand_projorder_budget_one
    (Realizable0 Realizable1 : (Bool -> Bool -> Bool) -> Prop)
    (h0 : ¬ Realizable0 (fun x y => !(x && y)))
    (h1 : Realizable1 (fun x y => !(x && y))) :
    ¬ Realizable0 (fun x y => !(x && y)) ∧
      Realizable1 (fun x y => !(x && y)) := by
  exact ⟨h0, h1⟩
