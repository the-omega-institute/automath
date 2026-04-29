import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete quotient-span certificate for the `rho_4,rho_5,rho_6` wall collapse.
The two wall congruences imply that every element in the span of the three potentials differs from
a rational multiple of `F5` by an element of the span of the fourth and sixth walls. If the primitive
fifth-wall witness says `F5` is not in the wall span, the quotient line is nonzero. -/
def conclusion_leyang_rho456_rank_one_collapse_mod_walls_claim : Prop :=
  ∀ {M : Type*} [AddCommGroup M] [Module ℚ M] (F4 F5 F6 wall4 wall6 : M),
    F6 - (5 / 6 : ℚ) • F5 = wall4 →
      F4 - (5 / 4 : ℚ) • F5 = wall6 →
        (∀ x ∈ Submodule.span ℚ ({F4, F5, F6} : Set M),
            ∃ a : ℚ, x - a • F5 ∈ Submodule.span ℚ ({wall4, wall6} : Set M)) ∧
          (F5 ∉ Submodule.span ℚ ({wall4, wall6} : Set M) →
            F5 ∈ Submodule.span ℚ ({F4, F5, F6} : Set M) ∧
              F5 ∉ Submodule.span ℚ ({wall4, wall6} : Set M))

/-- Paper label: `thm:conclusion-leyang-rho456-rank-one-collapse-mod-walls`. -/
theorem paper_conclusion_leyang_rho456_rank_one_collapse_mod_walls :
    conclusion_leyang_rho456_rank_one_collapse_mod_walls_claim := by
  intro M _ _ F4 F5 F6 wall4 wall6 h6 h4
  let walls : Submodule ℚ M := Submodule.span ℚ ({wall4, wall6} : Set M)
  refine ⟨?_, ?_⟩
  · intro x hx
    change x ∈ Submodule.span ℚ ({F4, F5, F6} : Set M) at hx
    refine Submodule.span_induction
      (s := ({F4, F5, F6} : Set M))
      (p := fun x _ => ∃ a : ℚ, x - a • F5 ∈ walls) ?_ ?_ ?_ ?_ hx
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy | hy
      · refine ⟨5 / 4, ?_⟩
        subst y
        change F4 - (5 / 4 : ℚ) • F5 ∈ walls
        rw [h4]
        exact Submodule.subset_span (by simp : wall6 ∈ ({wall4, wall6} : Set M))
      · refine ⟨1, ?_⟩
        subst y
        simp [walls]
      · refine ⟨5 / 6, ?_⟩
        subst y
        change F6 - (5 / 6 : ℚ) • F5 ∈ walls
        rw [h6]
        exact Submodule.subset_span (by simp : wall4 ∈ ({wall4, wall6} : Set M))
    · refine ⟨0, ?_⟩
      simp [walls]
    · intro x y _hx _hy hxWitness hyWitness
      rcases hxWitness with ⟨a, ha⟩
      rcases hyWitness with ⟨b, hb⟩
      refine ⟨a + b, ?_⟩
      have hsum : x + y - (a + b) • F5 = (x - a • F5) + (y - b • F5) := by
        module
      rw [hsum]
      exact walls.add_mem ha hb
    · intro c x _hx hxWitness
      rcases hxWitness with ⟨a, ha⟩
      refine ⟨c * a, ?_⟩
      have hsmul : c • x - (c * a) • F5 = c • (x - a • F5) := by
        module
      rw [hsmul]
      exact walls.smul_mem c ha
  · intro hprimitive
    exact ⟨Submodule.subset_span (by simp : F5 ∈ ({F4, F5, F6} : Set M)), hprimitive⟩

end Omega.Conclusion
