import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Concrete two-branch halting state used to synchronize the valuation, Walsh, and ledger
packages. -/
inductive paper_derived_halting_valuation_walsh_ledger_unification_halting_state where
  | diverges
  | haltsAt (N : ℕ)
  deriving DecidableEq

/-- The halting branch of the toy model. -/
def paper_derived_halting_valuation_walsh_ledger_unification_halts :
    paper_derived_halting_valuation_walsh_ledger_unification_halting_state → Prop
  | .diverges => False
  | .haltsAt _ => True

/-- The algebraic halting value `-2^(L N)` on the halting branch and `0` on the divergent branch. -/
def paper_derived_halting_valuation_walsh_ledger_unification_alpha (L : ℕ) :
    paper_derived_halting_valuation_walsh_ledger_unification_halting_state → ℤ
  | .diverges => 0
  | .haltsAt N => -((2 : ℤ) ^ (L * N))

/-- The dyadic valuation depth recorded by the halting branch. -/
def paper_derived_halting_valuation_walsh_ledger_unification_valuation_depth (L : ℕ) :
    paper_derived_halting_valuation_walsh_ledger_unification_halting_state → Option ℕ
  | .diverges => none
  | .haltsAt N => some (L * N)

/-- The first nontrivial Walsh breakpoint. -/
def paper_derived_halting_valuation_walsh_ledger_unification_walsh_breakpoint (L : ℕ) :
    paper_derived_halting_valuation_walsh_ledger_unification_halting_state → Option ℕ
  | .diverges => none
  | .haltsAt N => some (L * N + 1)

/-- The ledger kink profile: the halting branch plateaus at `N`, while the divergent branch keeps
growing linearly. -/
def paper_derived_halting_valuation_walsh_ledger_unification_ledger_profile :
    paper_derived_halting_valuation_walsh_ledger_unification_halting_state → ℕ → ℝ
  | .diverges, m => (m : ℝ) * Real.log 2
  | .haltsAt N, m => (min m N : ℝ) * Real.log 2

/-- The Hausdorff dimension proxy attached to the two branches. -/
def paper_derived_halting_valuation_walsh_ledger_unification_dimension (L : ℕ) :
    paper_derived_halting_valuation_walsh_ledger_unification_halting_state → ℝ
  | .diverges => 0
  | .haltsAt _ => 1 / (L : ℝ)

/-- The terminal atomic branch is exactly the divergent branch. -/
def paper_derived_halting_valuation_walsh_ledger_unification_atomic_branch :
    paper_derived_halting_valuation_walsh_ledger_unification_halting_state → Prop
  | .diverges => True
  | .haltsAt _ => False

/-- Paper label: `thm:derived-halting-valuation-walsh-ledger-unification`.
The same branch parameter controls the algebraic halting value, valuation depth, first Walsh
breakpoint, ledger plateau, and the terminal dimension/atomic split. -/
theorem paper_derived_halting_valuation_walsh_ledger_unification (L : ℕ) (hL : 0 < L) :
    ∀ σ : paper_derived_halting_valuation_walsh_ledger_unification_halting_state,
      (paper_derived_halting_valuation_walsh_ledger_unification_halts σ ↔
          paper_derived_halting_valuation_walsh_ledger_unification_alpha L σ ≠ 0) ∧
        (paper_derived_halting_valuation_walsh_ledger_unification_halts σ ↔
          (paper_derived_halting_valuation_walsh_ledger_unification_valuation_depth L σ).isSome) ∧
        (paper_derived_halting_valuation_walsh_ledger_unification_halts σ ↔
          (paper_derived_halting_valuation_walsh_ledger_unification_walsh_breakpoint L σ).isSome) ∧
        match σ with
        | .diverges =>
            paper_derived_halting_valuation_walsh_ledger_unification_alpha L σ = 0 ∧
              paper_derived_halting_valuation_walsh_ledger_unification_valuation_depth L σ = none ∧
              paper_derived_halting_valuation_walsh_ledger_unification_walsh_breakpoint L σ = none ∧
              (∀ m,
                paper_derived_halting_valuation_walsh_ledger_unification_ledger_profile σ m =
                  (m : ℝ) * Real.log 2) ∧
              paper_derived_halting_valuation_walsh_ledger_unification_dimension L σ = 0 ∧
              paper_derived_halting_valuation_walsh_ledger_unification_atomic_branch σ
        | .haltsAt N =>
            paper_derived_halting_valuation_walsh_ledger_unification_alpha L σ =
                -((2 : ℤ) ^ (L * N)) ∧
              paper_derived_halting_valuation_walsh_ledger_unification_valuation_depth L σ =
                some (L * N) ∧
              paper_derived_halting_valuation_walsh_ledger_unification_walsh_breakpoint L σ =
                some (L * N + 1) ∧
              (∀ m,
                paper_derived_halting_valuation_walsh_ledger_unification_ledger_profile σ m =
                  (min m N : ℝ) * Real.log 2) ∧
              0 < paper_derived_halting_valuation_walsh_ledger_unification_dimension L σ ∧
              paper_derived_halting_valuation_walsh_ledger_unification_dimension L σ =
                1 / (L : ℝ) ∧
              ¬ paper_derived_halting_valuation_walsh_ledger_unification_atomic_branch σ := by
  intro σ
  cases σ with
  | diverges =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [paper_derived_halting_valuation_walsh_ledger_unification_halts,
          paper_derived_halting_valuation_walsh_ledger_unification_alpha]
      · simp [paper_derived_halting_valuation_walsh_ledger_unification_halts,
          paper_derived_halting_valuation_walsh_ledger_unification_valuation_depth]
      · simp [paper_derived_halting_valuation_walsh_ledger_unification_halts,
          paper_derived_halting_valuation_walsh_ledger_unification_walsh_breakpoint]
      · refine ⟨rfl, rfl, rfl, ?_, rfl, trivial⟩
        intro m
        rfl
  | haltsAt N =>
      have hpow_ne : ((2 : ℤ) ^ (L * N)) ≠ 0 := by
        exact pow_ne_zero _ (by norm_num)
      have hL_real : 0 < (L : ℝ) := by
        exact_mod_cast hL
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [paper_derived_halting_valuation_walsh_ledger_unification_halts,
          paper_derived_halting_valuation_walsh_ledger_unification_alpha, hpow_ne]
      · simp [paper_derived_halting_valuation_walsh_ledger_unification_halts,
          paper_derived_halting_valuation_walsh_ledger_unification_valuation_depth]
      · simp [paper_derived_halting_valuation_walsh_ledger_unification_halts,
          paper_derived_halting_valuation_walsh_ledger_unification_walsh_breakpoint]
      · refine ⟨rfl, rfl, rfl, ?_, ?_, rfl, by simp
          [paper_derived_halting_valuation_walsh_ledger_unification_atomic_branch]⟩
        · intro m
          rfl
        · simp [paper_derived_halting_valuation_walsh_ledger_unification_dimension, one_div,
            hL_real]

end

end Omega.Conclusion
