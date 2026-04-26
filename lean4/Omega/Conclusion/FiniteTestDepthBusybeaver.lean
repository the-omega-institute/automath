import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

attribute [local instance] Classical.propDecidable

/-- Concrete finite-family package for the test-depth / Busy Beaver comparison. A program `M`
is encoded by the total `0/1` function `code M`, the comparator `constantOne` computes the
constant-one function, and `code_spec` says the derived function stays equal to `1` exactly up to
the halting time of `M`. Hence the first disagreement depth is the halting time itself. -/
structure conclusion_finite_test_depth_busybeaver_data where
  program : Type
  instFintype : Fintype program
  instDecidableEq : DecidableEq program
  size : program → ℕ
  bound : ℕ
  haltingTime : program → ℕ
  code : program → ℕ → Bool
  constantOne : program
  constantOne_spec : ∀ n, code constantOne n = true
  code_spec : ∀ M n, code M n = decide (n < haltingTime M)

attribute [instance] conclusion_finite_test_depth_busybeaver_data.instFintype
attribute [instance] conclusion_finite_test_depth_busybeaver_data.instDecidableEq

namespace conclusion_finite_test_depth_busybeaver_data

/-- The programs whose size is at most the ambient bound. -/
def bounded_programs (D : conclusion_finite_test_depth_busybeaver_data) : Finset D.program :=
  Finset.univ.filter fun M => D.size M ≤ D.bound

lemma disagreement_exists (D : conclusion_finite_test_depth_busybeaver_data) (M : D.program) :
    ∃ n, D.code M n ≠ D.code D.constantOne n := by
  refine ⟨D.haltingTime M, ?_⟩
  rw [D.code_spec, D.constantOne_spec]
  simp

/-- The first depth at which the derived function disagrees with the constant-one comparator. -/
noncomputable def first_disagreement_depth (D : conclusion_finite_test_depth_busybeaver_data)
    (M : D.program) : ℕ :=
  Nat.find (D.disagreement_exists M)

lemma first_disagreement_depth_eq_haltingTime
    (D : conclusion_finite_test_depth_busybeaver_data) (M : D.program) :
    D.first_disagreement_depth M = D.haltingTime M := by
  have hAt :
      D.code M (D.haltingTime M) ≠ D.code D.constantOne (D.haltingTime M) := by
    rw [D.code_spec, D.constantOne_spec]
    simp
  have hle : D.first_disagreement_depth M ≤ D.haltingTime M :=
    Nat.find_min' _ hAt
  have hspec :
      D.code M (D.first_disagreement_depth M) ≠
        D.code D.constantOne (D.first_disagreement_depth M) :=
    Nat.find_spec (D.disagreement_exists M)
  have hge : D.haltingTime M ≤ D.first_disagreement_depth M := by
    by_contra hlt
    have hlt' : D.first_disagreement_depth M < D.haltingTime M := Nat.lt_of_not_ge hlt
    have hcode : D.code M (D.first_disagreement_depth M) = true := by
      rw [D.code_spec]
      simp [hlt']
    have hone : D.code D.constantOne (D.first_disagreement_depth M) = true :=
      D.constantOne_spec _
    exact hspec (by rw [hcode, hone])
  exact le_antisymm hle hge

/-- Supremum of halting times over the size-bounded family. -/
def busy_beaver_at (D : conclusion_finite_test_depth_busybeaver_data) : ℕ :=
  D.bounded_programs.sup D.haltingTime

/-- Supremum of first disagreement depths over the same size-bounded family. -/
noncomputable def finite_test_depth_at (D : conclusion_finite_test_depth_busybeaver_data) : ℕ :=
  D.bounded_programs.sup D.first_disagreement_depth

/-- The test-depth frontier dominates the Busy Beaver frontier. -/
def busy_beaver_lower_bound (D : conclusion_finite_test_depth_busybeaver_data) : Prop :=
  D.busy_beaver_at ≤ D.finite_test_depth_at

end conclusion_finite_test_depth_busybeaver_data

/-- Paper label: `thm:conclusion-finite-test-depth-busybeaver`. -/
theorem paper_conclusion_finite_test_depth_busybeaver
    (D : conclusion_finite_test_depth_busybeaver_data) :
    D.busy_beaver_lower_bound := by
  rw [conclusion_finite_test_depth_busybeaver_data.busy_beaver_lower_bound,
    conclusion_finite_test_depth_busybeaver_data.busy_beaver_at,
    conclusion_finite_test_depth_busybeaver_data.finite_test_depth_at, Finset.sup_le_iff]
  intro M hM
  calc
    D.haltingTime M = D.first_disagreement_depth M := by
      symm
      exact D.first_disagreement_depth_eq_haltingTime M
    _ ≤ D.bounded_programs.sup D.first_disagreement_depth := Finset.le_sup hM

end Omega.Conclusion
