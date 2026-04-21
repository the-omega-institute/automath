import Omega.POM.FractranPrimecoreFinitePartialFunctionCategory

namespace Omega.POM

private lemma eval_map_some_of_mem {X : Type} [DecidableEq X] (f : X → X) :
    ∀ {l : List X}, l.Nodup → ∀ {x : X}, x ∈ l →
      evalFracPPBotProgram (l.map fun y => (some y, some (f y))) (some x) = some (f x)
  | [], _, _, hx => by cases hx
  | y :: l, hnodup, x, hx => by
      rcases List.nodup_cons.mp hnodup with ⟨hy, htail⟩
      rcases List.mem_cons.mp hx with rfl | hx'
      · simp [evalFracPPBotProgram]
      · have hne : y ≠ x := by
          intro h
          apply hy
          simpa [h] using hx'
        simp [evalFracPPBotProgram, hne, eval_map_some_of_mem f htail hx']

/-- A total finite update table is realized by the canonical prime-core first-fit program attached
to the total partial map `x ↦ some (f x)`.
    cor:pom-fractran-finite-update-table-one-step -/
theorem paper_pom_fractran_finite_update_table_one_step (X : Type) [Fintype X] [DecidableEq X]
    (f : X → X) : ∃ F : FracPPBotProgram X, fracPPBotProgramToPartialMap F = fun x => some (f x) := by
  classical
  refine ⟨Finset.univ.toList.map fun x => (some x, some (f x)), ?_⟩
  funext x
  simp [fracPPBotProgramToPartialMap, eval_map_some_of_mem f (Finset.nodup_toList (s := Finset.univ)),
    Finset.mem_toList]

end Omega.POM
