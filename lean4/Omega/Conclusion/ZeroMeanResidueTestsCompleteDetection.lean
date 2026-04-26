import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

noncomputable section

/-- Chapter-local zero-mean condition after removing the trivial residue channel. -/
def conclusion_zero_mean_residue_tests_complete_detection_zero_mean {q : ℕ} [NeZero q]
    (b : Fin q → Complex) : Prop :=
  b 0 = 0

/-- Residue limits built from the constant term and the nontrivial residue modes. -/
def conclusion_zero_mean_residue_tests_complete_detection_residue_limit {q : ℕ} [NeZero q]
    (c : Fin q → Complex) (r : Fin q) : Complex :=
  if r = 0 then c 0 else c 0 + c r

/-- The normalized residue test, already expanded onto the nontrivial Fourier channels. -/
def conclusion_zero_mean_residue_tests_complete_detection_test_limit {q : ℕ} [NeZero q]
    (c b : Fin q → Complex) : Complex :=
  Finset.sum (Finset.univ.erase 0) (fun r => b r * c r)

/-- Vanishing of all nontrivial Fourier modes. -/
def conclusion_zero_mean_residue_tests_complete_detection_nontrivial_modes_vanish {q : ℕ}
    [NeZero q] (c : Fin q → Complex) : Prop :=
  ∀ r : Fin q, r ≠ 0 → c r = 0

/-- Equality of all residue limits. -/
def conclusion_zero_mean_residue_tests_complete_detection_equal_residue_limits {q : ℕ} [NeZero q]
    (c : Fin q → Complex) : Prop :=
  ∀ r : Fin q,
    conclusion_zero_mean_residue_tests_complete_detection_residue_limit c r =
      conclusion_zero_mean_residue_tests_complete_detection_residue_limit c 0

/-- The `q`-power factorization condition in the chapter-local model. -/
def conclusion_zero_mean_residue_tests_complete_detection_q_power_factorization {q : ℕ}
    [NeZero q] (c : Fin q → Complex) : Prop :=
  ∀ r : Fin q, r ≠ 0 → c r = 0

/-- Basis vector detecting the `s`-th nontrivial mode. -/
def conclusion_zero_mean_residue_tests_complete_detection_basis_weight {q : ℕ} [NeZero q]
    (s : Fin q) : Fin q → Complex :=
  fun r => if r = s then 1 else 0

lemma conclusion_zero_mean_residue_tests_complete_detection_basis_weight_zero_mean {q : ℕ}
    [NeZero q] {s : Fin q} (hs : s ≠ 0) :
    conclusion_zero_mean_residue_tests_complete_detection_zero_mean
      (conclusion_zero_mean_residue_tests_complete_detection_basis_weight s) := by
  have h0s : (0 : Fin q) ≠ s := by
    simpa [eq_comm] using hs
  simp [conclusion_zero_mean_residue_tests_complete_detection_zero_mean,
    conclusion_zero_mean_residue_tests_complete_detection_basis_weight, h0s]

lemma conclusion_zero_mean_residue_tests_complete_detection_basis_weight_test_limit {q : ℕ}
    [NeZero q] (c : Fin q → Complex) {s : Fin q} (hs : s ≠ 0) :
    conclusion_zero_mean_residue_tests_complete_detection_test_limit c
        (conclusion_zero_mean_residue_tests_complete_detection_basis_weight s) =
      c s := by
  unfold conclusion_zero_mean_residue_tests_complete_detection_test_limit
  have hs_mem : s ∈ (Finset.univ.erase (0 : Fin q) : Finset (Fin q)) := by simp [hs]
  have hsingle :
      Finset.sum (Finset.univ.erase 0)
        (fun r =>
          conclusion_zero_mean_residue_tests_complete_detection_basis_weight s r * c r) =
        conclusion_zero_mean_residue_tests_complete_detection_basis_weight s s * c s := by
    refine Finset.sum_eq_single s ?_ ?_
    · intro r hr hrs
      have hrs' : r ≠ s := by simpa using hrs
      simp [conclusion_zero_mean_residue_tests_complete_detection_basis_weight, hrs']
    · intro hs_not_mem
      exact False.elim (hs_not_mem hs_mem)
  simpa [conclusion_zero_mean_residue_tests_complete_detection_basis_weight] using hsingle

lemma conclusion_zero_mean_residue_tests_complete_detection_nontrivial_iff_equal {q : ℕ}
    [NeZero q] (c : Fin q → Complex) :
    conclusion_zero_mean_residue_tests_complete_detection_nontrivial_modes_vanish c ↔
      conclusion_zero_mean_residue_tests_complete_detection_equal_residue_limits c := by
  constructor
  · intro hvanish r
    by_cases hr : r = 0
    · simp [conclusion_zero_mean_residue_tests_complete_detection_residue_limit, hr]
    · have hcr : c r = 0 := hvanish r hr
      simp [conclusion_zero_mean_residue_tests_complete_detection_residue_limit, hr, hcr]
  · intro heq r hr
    have hEq := heq r
    simp [conclusion_zero_mean_residue_tests_complete_detection_residue_limit, hr] at hEq
    exact hEq

/-- Paper label: `thm:conclusion-zero-mean-residue-tests-complete-detection`.
In the chapter-local model, the zero-mean residue tests are exactly the linear probes of the
nontrivial residue modes. The basis probes isolate each nonzero mode, so vanishing of all tests
is equivalent to vanishing of every nontrivial Fourier mode, equality of all residue limits, and
the `q`-power factorization condition. -/
theorem paper_conclusion_zero_mean_residue_tests_complete_detection {q : ℕ} [NeZero q]
    (_hq : 2 ≤ q) (c : Fin q → Complex) :
    (∀ b : Fin q → Complex,
      conclusion_zero_mean_residue_tests_complete_detection_zero_mean b →
        conclusion_zero_mean_residue_tests_complete_detection_test_limit c b =
          Finset.sum (Finset.univ.erase 0) (fun r => b r * c r)) ∧
      ((∀ b : Fin q → Complex,
          conclusion_zero_mean_residue_tests_complete_detection_zero_mean b →
            conclusion_zero_mean_residue_tests_complete_detection_test_limit c b = 0) ↔
        conclusion_zero_mean_residue_tests_complete_detection_nontrivial_modes_vanish c) ∧
      (conclusion_zero_mean_residue_tests_complete_detection_nontrivial_modes_vanish c ↔
        conclusion_zero_mean_residue_tests_complete_detection_equal_residue_limits c) ∧
      (conclusion_zero_mean_residue_tests_complete_detection_nontrivial_modes_vanish c ↔
        conclusion_zero_mean_residue_tests_complete_detection_q_power_factorization c) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b _hb
    rfl
  · constructor
    · intro htest r hr
      have hbasis := htest
        (conclusion_zero_mean_residue_tests_complete_detection_basis_weight r)
        (conclusion_zero_mean_residue_tests_complete_detection_basis_weight_zero_mean hr)
      rw [conclusion_zero_mean_residue_tests_complete_detection_basis_weight_test_limit c hr] at hbasis
      exact hbasis
    · intro hvanish b _hb
      unfold conclusion_zero_mean_residue_tests_complete_detection_test_limit
      refine Finset.sum_eq_zero ?_
      intro r hr
      have hr0 : r ≠ 0 := by simpa using hr
      simp [hvanish r hr0]
  · exact conclusion_zero_mean_residue_tests_complete_detection_nontrivial_iff_equal c
  · rfl

end

end Omega.Conclusion
