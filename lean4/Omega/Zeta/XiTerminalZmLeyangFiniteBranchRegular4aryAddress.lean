import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite-level and inverse-limit address data for the five-sheet Lee--Yang tower. -/
structure xi_terminal_zm_leyang_finite_branch_regular_4ary_address_data where
  xi_terminal_zm_leyang_finite_branch_regular_4ary_address_finiteBranch :
    Fin 5 → ℕ → Type
  xi_terminal_zm_leyang_finite_branch_regular_4ary_address_finiteBranchEquiv :
    ∀ i n,
      xi_terminal_zm_leyang_finite_branch_regular_4ary_address_finiteBranch i n ≃ Fin (4 ^ n)
  xi_terminal_zm_leyang_finite_branch_regular_4ary_address_limitBranch : Fin 5 → Type
  xi_terminal_zm_leyang_finite_branch_regular_4ary_address_limitBranchEquiv :
    ∀ i,
      xi_terminal_zm_leyang_finite_branch_regular_4ary_address_limitBranch i ≃ (ℕ → Fin 4)

/-- The one-step branch cover splits as a base address of length `n` together with one new
quaternary digit. -/
def xi_terminal_zm_leyang_finite_branch_regular_4ary_address_oneStepEquiv
    (D : xi_terminal_zm_leyang_finite_branch_regular_4ary_address_data) (i : Fin 5) (n : ℕ) :
    D.xi_terminal_zm_leyang_finite_branch_regular_4ary_address_finiteBranch i (n + 1) ≃
      D.xi_terminal_zm_leyang_finite_branch_regular_4ary_address_finiteBranch i n × Fin 4 :=
  (D.xi_terminal_zm_leyang_finite_branch_regular_4ary_address_finiteBranchEquiv i (n + 1)).trans <|
    (finCongr (by rw [pow_succ])).trans <|
      finProdFinEquiv.symm.trans <|
        Equiv.prodCongr
          (D.xi_terminal_zm_leyang_finite_branch_regular_4ary_address_finiteBranchEquiv i n).symm
          (Equiv.refl _)

/-- The `r`-step branch cover splits as an old address together with an independent length-`r`
quaternary tail. -/
def xi_terminal_zm_leyang_finite_branch_regular_4ary_address_rStepEquiv
    (D : xi_terminal_zm_leyang_finite_branch_regular_4ary_address_data) (i : Fin 5)
    (n r : ℕ) :
    D.xi_terminal_zm_leyang_finite_branch_regular_4ary_address_finiteBranch i (n + r) ≃
      D.xi_terminal_zm_leyang_finite_branch_regular_4ary_address_finiteBranch i n ×
        Fin (4 ^ r) :=
  (D.xi_terminal_zm_leyang_finite_branch_regular_4ary_address_finiteBranchEquiv i (n + r)).trans <|
    (finCongr (by rw [pow_add])).trans <|
      finProdFinEquiv.symm.trans <|
        Equiv.prodCongr
          (D.xi_terminal_zm_leyang_finite_branch_regular_4ary_address_finiteBranchEquiv i n).symm
          (Equiv.refl _)

/-- The disjoint union of the five inverse-limit sheets. -/
def xi_terminal_zm_leyang_finite_branch_regular_4ary_address_limitUnion
    (D : xi_terminal_zm_leyang_finite_branch_regular_4ary_address_data) :=
  Σ i : Fin 5, D.xi_terminal_zm_leyang_finite_branch_regular_4ary_address_limitBranch i

/-- Choosing compatible lifts identifies the inverse-limit tower with five parallel `2`-adic
address sheets, encoded here as quaternary streams. -/
def xi_terminal_zm_leyang_finite_branch_regular_4ary_address_limitEquiv
    (D : xi_terminal_zm_leyang_finite_branch_regular_4ary_address_data) :
    xi_terminal_zm_leyang_finite_branch_regular_4ary_address_limitUnion D ≃
      Fin 5 × (ℕ → Fin 4) :=
  Equiv.sigmaEquivProdOfEquiv
    (fun i =>
      D.xi_terminal_zm_leyang_finite_branch_regular_4ary_address_limitBranchEquiv i)

/-- The finite Lee--Yang branch tower has a regular quaternary address structure: every sheet is
four-to-one at one step, `4^r`-to-one after `r` steps, and the inverse limit splits as five
parallel quaternary address sheets. -/
def xi_terminal_zm_leyang_finite_branch_regular_4ary_address_data.has_regular_4ary_address
    (D : xi_terminal_zm_leyang_finite_branch_regular_4ary_address_data) : Prop :=
  (∀ i n,
    Nonempty
      (D.xi_terminal_zm_leyang_finite_branch_regular_4ary_address_finiteBranch i (n + 1) ≃
        D.xi_terminal_zm_leyang_finite_branch_regular_4ary_address_finiteBranch i n × Fin 4)) ∧
  (∀ i n r, 1 ≤ r →
    Nonempty
      (D.xi_terminal_zm_leyang_finite_branch_regular_4ary_address_finiteBranch i (n + r) ≃
        D.xi_terminal_zm_leyang_finite_branch_regular_4ary_address_finiteBranch i n ×
          Fin (4 ^ r))) ∧
  Nonempty
    (xi_terminal_zm_leyang_finite_branch_regular_4ary_address_limitUnion D ≃
      Fin 5 × (ℕ → Fin 4))

/-- Paper label: `cor:xi-terminal-zm-leyang-finite-branch-regular-4ary-address`. -/
theorem paper_xi_terminal_zm_leyang_finite_branch_regular_4ary_address
    (D : xi_terminal_zm_leyang_finite_branch_regular_4ary_address_data) :
    D.has_regular_4ary_address := by
  refine ⟨?_, ?_, ?_⟩
  · intro i n
    exact ⟨xi_terminal_zm_leyang_finite_branch_regular_4ary_address_oneStepEquiv D i n⟩
  · intro i n r hr
    let _ := hr
    exact ⟨xi_terminal_zm_leyang_finite_branch_regular_4ary_address_rStepEquiv D i n r⟩
  · exact ⟨xi_terminal_zm_leyang_finite_branch_regular_4ary_address_limitEquiv D⟩

end Omega.Zeta
