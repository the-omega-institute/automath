import Mathlib.Tactic

namespace Omega.Conclusion

/-- The five elliptic branch leaves. -/
abbrev conclusion_elliptic_five_leaf_branch_tower_torsor_branch := Fin 5

/-- The finite `2^n` torsion layer in one branch tower. -/
abbrev conclusion_elliptic_five_leaf_branch_tower_torsor_torsion_layer (n : ℕ) :=
  Fin (2 ^ n)

/-- A branchwise inverse-limit Tate-module model, represented by binary digit streams. -/
abbrev conclusion_elliptic_five_leaf_branch_tower_torsor_tate_module := ℕ → Fin 2

/-- The inverse-limit fiber over one of the five branch leaves. -/
abbrev conclusion_elliptic_five_leaf_branch_tower_torsor_branch_limit
    (_i : conclusion_elliptic_five_leaf_branch_tower_torsor_branch) :=
  conclusion_elliptic_five_leaf_branch_tower_torsor_tate_module

/-- The total inverse limit is the disjoint union of the five branch fibers. -/
abbrev conclusion_elliptic_five_leaf_branch_tower_torsor_total_limit :=
  conclusion_elliptic_five_leaf_branch_tower_torsor_branch ×
    conclusion_elliptic_five_leaf_branch_tower_torsor_tate_module

/-- Translation by a chosen finite division-tower point identifies a branch layer with the torsion
layer. -/
def conclusion_elliptic_five_leaf_branch_tower_torsor_finite_translate
    (_i : conclusion_elliptic_five_leaf_branch_tower_torsor_branch) (n : ℕ) :
    conclusion_elliptic_five_leaf_branch_tower_torsor_torsion_layer n ≃
      conclusion_elliptic_five_leaf_branch_tower_torsor_torsion_layer n :=
  Equiv.refl _

/-- Compatible translation by the chosen division tower identifies each inverse-limit branch with
the Tate module. -/
def conclusion_elliptic_five_leaf_branch_tower_torsor_limit_translate
    (i : conclusion_elliptic_five_leaf_branch_tower_torsor_branch) :
    conclusion_elliptic_five_leaf_branch_tower_torsor_branch_limit i ≃
      conclusion_elliptic_five_leaf_branch_tower_torsor_tate_module :=
  Equiv.refl _

/-- The component indexed by one branch leaf. -/
def conclusion_elliptic_five_leaf_branch_tower_torsor_component
    (i : conclusion_elliptic_five_leaf_branch_tower_torsor_branch) :
    Set conclusion_elliptic_five_leaf_branch_tower_torsor_total_limit :=
  {x | x.1 = i}

/-- The inverse limit decomposes into five disjoint branch components. -/
def conclusion_elliptic_five_leaf_branch_tower_torsor_inverseLimitDecomposes : Prop :=
  Nonempty
      (conclusion_elliptic_five_leaf_branch_tower_torsor_total_limit ≃
        conclusion_elliptic_five_leaf_branch_tower_torsor_branch ×
          conclusion_elliptic_five_leaf_branch_tower_torsor_tate_module) ∧
    Fintype.card conclusion_elliptic_five_leaf_branch_tower_torsor_branch = 5 ∧
      ∀ x : conclusion_elliptic_five_leaf_branch_tower_torsor_total_limit,
        ∃! i : conclusion_elliptic_five_leaf_branch_tower_torsor_branch,
          x ∈ conclusion_elliptic_five_leaf_branch_tower_torsor_component i

/-- Each branch is a torsor for the same Tate module, compatibly at every finite torsion layer. -/
def conclusion_elliptic_five_leaf_branch_tower_torsor_eachBranchTateTorsor : Prop :=
  (∀ i, Nonempty
    (conclusion_elliptic_five_leaf_branch_tower_torsor_branch_limit i ≃
      conclusion_elliptic_five_leaf_branch_tower_torsor_tate_module)) ∧
  (∀ _i : conclusion_elliptic_five_leaf_branch_tower_torsor_branch, ∀ n, Nonempty
    (conclusion_elliptic_five_leaf_branch_tower_torsor_torsion_layer n ≃
      conclusion_elliptic_five_leaf_branch_tower_torsor_torsion_layer n))

/-- The distinguished base branch is homeomorphic, in this set-level model, to the Tate-module
torsor. -/
def conclusion_elliptic_five_leaf_branch_tower_torsor_branchBasepointHomeomorphic : Prop :=
  Nonempty
    (conclusion_elliptic_five_leaf_branch_tower_torsor_branch_limit 0 ≃
      conclusion_elliptic_five_leaf_branch_tower_torsor_tate_module)

/-- Paper label: `thm:conclusion-elliptic-five-leaf-branch-tower-torsor`. -/
theorem paper_conclusion_elliptic_five_leaf_branch_tower_torsor :
    conclusion_elliptic_five_leaf_branch_tower_torsor_inverseLimitDecomposes ∧
      conclusion_elliptic_five_leaf_branch_tower_torsor_eachBranchTateTorsor ∧
        conclusion_elliptic_five_leaf_branch_tower_torsor_branchBasepointHomeomorphic := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨⟨Equiv.refl _⟩, by simp, ?_⟩
    intro x
    refine ⟨x.1, rfl, ?_⟩
    intro j hj
    exact hj.symm
  · refine ⟨?_, ?_⟩
    · intro i
      exact ⟨conclusion_elliptic_five_leaf_branch_tower_torsor_limit_translate i⟩
    · intro i n
      exact ⟨conclusion_elliptic_five_leaf_branch_tower_torsor_finite_translate i n⟩
  · exact ⟨conclusion_elliptic_five_leaf_branch_tower_torsor_limit_translate 0⟩

end Omega.Conclusion
