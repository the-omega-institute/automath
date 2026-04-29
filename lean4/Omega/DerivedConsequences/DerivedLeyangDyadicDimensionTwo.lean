import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Zeta.DerivedLeyangProfiniteRigidity
import Omega.Zeta.XiTerminalZmLeyangFiniteBranchRegular4aryAddress

namespace Omega.DerivedConsequences

open Omega.Zeta

/-- The quaternary dyadic dimension read off from exact `4^n` cylinder counts. -/
noncomputable def derived_leyang_dyadic_dimension_two_dimension : ℝ :=
  Real.log 4 / Real.log 2

/-- Paper label: `cor:derived-leyang-dyadic-dimension-two`. The verified regular `4`-ary address
structure gives exact `4^n` cylinder counts on every sheet and identifies each inverse-limit sheet
with a quaternary stream space. Combined with the profinite-rigidity entropy identity
`log 4 = 2 log 2`, this fixes the dyadic dimension to `2`. -/
theorem paper_derived_leyang_dyadic_dimension_two
    (D : xi_terminal_zm_leyang_finite_branch_regular_4ary_address_data) :
    D.has_regular_4ary_address ∧
      (∀ i n,
        Nonempty
          (D.xi_terminal_zm_leyang_finite_branch_regular_4ary_address_finiteBranch i n ≃
            Fin (4 ^ n))) ∧
      (∀ i,
        Nonempty
          (D.xi_terminal_zm_leyang_finite_branch_regular_4ary_address_limitBranch i ≃
            (ℕ → Fin 4))) ∧
      derived_leyang_dyadic_dimension_two_dimension = 2 := by
  have hregular := paper_xi_terminal_zm_leyang_finite_branch_regular_4ary_address D
  have hlog :
      Real.log 4 = 2 * Real.log 2 := by
    exact (paper_derived_leyang_profinite_rigidity True True (Real.log 4) rfl trivial trivial).2.2
  refine ⟨hregular, ?_, ?_, ?_⟩
  · intro i n
    exact ⟨D.xi_terminal_zm_leyang_finite_branch_regular_4ary_address_finiteBranchEquiv i n⟩
  · intro i
    exact ⟨D.xi_terminal_zm_leyang_finite_branch_regular_4ary_address_limitBranchEquiv i⟩
  · unfold derived_leyang_dyadic_dimension_two_dimension
    have hlog2_ne : Real.log 2 ≠ 0 := by
      have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      linarith
    apply (div_eq_iff hlog2_ne).2
    rw [hlog]

end Omega.DerivedConsequences
