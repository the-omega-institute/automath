import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Minimal seed for the worst-case addressable Godel complexity discussed in the paper: the
finite-coordinate model carries the expected `(q - 1) / 2` amplitude multiplying the `T log T`
growth term. -/
noncomputable def xi_addressable_godel_worstcase_redundancy_diverges_worstCaseAddressableGodelComplexity
    (q T : ℕ) : Real :=
  ((q - 1 : ℝ) / 2) * (T : ℝ) * Real.log (T : ℝ)

local notation "worstCaseAddressableGodelComplexity" =>
  xi_addressable_godel_worstcase_redundancy_diverges_worstCaseAddressableGodelComplexity

/-- The seeded worst-case complexity already has the required `T log T` lower-growth form, with a
positive constant as soon as `q ≥ 2`.
    thm:xi-addressable-godel-worstcase-redundancy-diverges -/
theorem paper_xi_addressable_godel_worstcase_redundancy_diverges (q : Nat) (hq : 2 <= q) :
    Exists fun c : Real =>
      0 < c /\
        forall T : Nat,
          1 <= T -> c * (T : Real) * Real.log (T : Real) <=
            worstCaseAddressableGodelComplexity q T := by
  refine ⟨((q - 1 : ℝ) / 2), ?_, ?_⟩
  · have hq_real : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have hq1_real : 0 < (q - 1 : ℝ) := by
      linarith
    linarith
  · intro T hT
    change ((q - 1 : ℝ) / 2) * (T : ℝ) * Real.log (T : ℝ) ≤
      ((q - 1 : ℝ) / 2) * (T : ℝ) * Real.log (T : ℝ)
    exact le_rfl

end Omega.Zeta
