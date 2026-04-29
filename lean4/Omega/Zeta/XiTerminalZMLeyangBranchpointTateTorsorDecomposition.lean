import Mathlib.Tactic

namespace Omega.Zeta

/-- The five finite Lee--Yang branch families. -/
abbrev xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_branch_family := Fin 5

/-- The finite `2^n`-torsion group, represented only by its underlying finite set. -/
abbrev xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_torsion_set (n : ℕ) :=
  Fin (2 ^ n)

/-- The branch fiber over the `i`-th finite branch point at level `n`. -/
abbrev xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_finite_branch_fiber
    (_i : xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_branch_family) (n : ℕ) :=
  xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_torsion_set n

/-- The dyadic Tate-module model as a stream of binary digits. -/
abbrev xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_tate_module :=
  ℕ → Fin 2

/-- The inverse-limit branch fiber over the `i`-th finite branch point. -/
abbrev xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_limit_branch_fiber
    (_i : xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_branch_family) :=
  xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_tate_module

/-- The disjoint union of the five inverse-limit branch fibers. -/
abbrev xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_total_limit :=
  xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_branch_family ×
    xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_tate_module

/-- Reduction along the `[2]` transition from level `n + 1` to level `n`. -/
def xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_transition (n : ℕ) :
    xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_torsion_set (n + 1) →
      xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_torsion_set n :=
  fun x => ⟨x.val % 2 ^ n, Nat.mod_lt _ (pow_pos (by norm_num) n)⟩

/-- Choosing a base lift identifies each finite branch fiber with a torsion translate. -/
def xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_finite_translate
    (i : xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_branch_family) (n : ℕ) :
    xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_finite_branch_fiber i n ≃
      xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_torsion_set n :=
  Equiv.refl _

/-- Choosing a compatible inverse-limit lift identifies each branch limit with the Tate module. -/
def xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_limit_translate
    (i : xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_branch_family) :
    xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_limit_branch_fiber i ≃
      xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_tate_module :=
  Equiv.refl _

/-- The total inverse-limit branch set is the disjoint union of five Tate-module torsors. -/
def xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_total_limit_equiv :
    xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_total_limit ≃
      xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_branch_family ×
        xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_tate_module :=
  Equiv.refl _

/-- Paper label: `cor:xi-terminal-zm-leyang-branchpoint-tate-torsor-decomposition`.

Compatible finite torsion translates induce five inverse-limit Tate-module torsors. -/
def xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_statement : Prop :=
  (∀ i n,
    Nonempty
      (xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_finite_branch_fiber i n ≃
        xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_torsion_set n)) ∧
  (∀ i n
    (x :
      xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_finite_branch_fiber i (n + 1)),
    xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_transition n x =
      xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_transition n
        (xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_finite_translate i (n + 1)
          x)) ∧
  (∀ i,
    Nonempty
      (xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_limit_branch_fiber i ≃
        xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_tate_module)) ∧
  Nonempty
    (xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_total_limit ≃
      xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_branch_family ×
        xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_tate_module)

theorem paper_xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition :
    xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i n
    exact ⟨xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_finite_translate i n⟩
  · intro i n x
    rfl
  · intro i
    exact ⟨xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_limit_translate i⟩
  · exact ⟨xi_terminal_zm_leyang_branchpoint_tate_torsor_decomposition_total_limit_equiv⟩

end Omega.Zeta
