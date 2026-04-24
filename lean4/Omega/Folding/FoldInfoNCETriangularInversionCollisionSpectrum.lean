import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Folding.FoldInfoNCEBayesInfoncePowerSumExpansion

namespace Omega.Folding

open scoped BigOperators

noncomputable section

/-- The forward-difference coefficient of `f(j) = log (1 + j)` appearing in the triangular
Bayes-InfoNCE loss tower. -/
def foldInfoNCEForwardDifferenceCoeff (t : ℕ) : ℝ :=
  Finset.sum (Finset.range (t + 1)) fun j =>
    ((-1 : ℝ) ^ (t - j)) * (Nat.choose t j : ℝ) * Real.log (j + 1)

/-- The finite loss tower is lower triangular in the normalized collision moments, the diagonal
coefficient is the forward-difference/log-coefficient rewrite, and whenever that diagonal entry is
nonzero the top moment is recovered by solving the last term explicitly. -/
def foldInfoNCETriangularInversionCollisionSpectrumStatement (m Q : Nat) : Prop :=
  ∀ n ∈ Finset.Icc 1 Q,
    Omega.OperatorAlgebra.foldInfoNCEFiniteKMomentExpansion m (n + 1) =
        Finset.sum (Finset.Icc 1 n) (fun t =>
          (Nat.choose n t : ℝ) * foldInfoNCEForwardDifferenceCoeff t *
            Omega.OperatorAlgebra.foldCollisionMomentNormalized (t + 1) m) ∧
      foldInfoNCEForwardDifferenceCoeff n = ((-1 : ℝ) ^ (n + 1)) * foldInfoNCEAlpha n ∧
      (foldInfoNCEForwardDifferenceCoeff n ≠ 0 →
        Omega.OperatorAlgebra.foldCollisionMomentNormalized (n + 1) m =
          (Omega.OperatorAlgebra.foldInfoNCEFiniteKMomentExpansion m (n + 1) -
            Finset.sum (Finset.Icc 1 (n - 1)) (fun t =>
              (Nat.choose n t : ℝ) * foldInfoNCEForwardDifferenceCoeff t *
                Omega.OperatorAlgebra.foldCollisionMomentNormalized (t + 1) m)) /
            foldInfoNCEForwardDifferenceCoeff n)

private lemma neg_one_pow_add_two (n : ℕ) : (-1 : ℝ) ^ (n + 2) = (-1 : ℝ) ^ n := by
  rw [pow_add]
  norm_num

private lemma foldInfoNCEForwardDifferenceCoeff_eq_signedSum (t : ℕ) :
    foldInfoNCEForwardDifferenceCoeff t =
      (-1 : ℝ) ^ t *
        Finset.sum (Finset.range (t + 1)) (fun j =>
          ((-1 : ℝ) ^ j) * (Nat.choose t j : ℝ) * Real.log (j + 1)) := by
  unfold foldInfoNCEForwardDifferenceCoeff
  calc
    ∑ j ∈ Finset.range (t + 1), (-1 : ℝ) ^ (t - j) * (Nat.choose t j : ℝ) * Real.log (j + 1) =
        ∑ j ∈ Finset.range (t + 1),
          ((-1 : ℝ) ^ t) * (((-1 : ℝ) ^ j) * (Nat.choose t j : ℝ) * Real.log (j + 1)) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            have hj' : j ≤ t := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
            rw [Omega.OperatorAlgebra.neg_one_pow_sub_eq_mul_neg_one_pow t j hj']
            ring
    _ = (-1 : ℝ) ^ t *
          Finset.sum (Finset.range (t + 1)) (fun j =>
            ((-1 : ℝ) ^ j) * (Nat.choose t j : ℝ) * Real.log (j + 1)) := by
          rw [Finset.mul_sum]

private lemma foldInfoNCEForwardDifferenceCoeff_eq_alpha (t : ℕ) :
    foldInfoNCEForwardDifferenceCoeff t = ((-1 : ℝ) ^ (t + 1)) * foldInfoNCEAlpha t := by
  have hsum :
      Finset.sum (Finset.range (t + 1)) (fun j =>
        ((-1 : ℝ) ^ j) * (Nat.choose t j : ℝ) * Real.log (j + 1)) = -foldInfoNCEAlpha t := by
    linarith [paper_fold_infonce_alpha_log_closed_form t]
  calc
    foldInfoNCEForwardDifferenceCoeff t =
        (-1 : ℝ) ^ t *
          Finset.sum (Finset.range (t + 1)) (fun j =>
            ((-1 : ℝ) ^ j) * (Nat.choose t j : ℝ) * Real.log (j + 1)) :=
      foldInfoNCEForwardDifferenceCoeff_eq_signedSum t
    _ = (-1 : ℝ) ^ t * (-foldInfoNCEAlpha t) := by rw [hsum]
    _ = ((-1 : ℝ) ^ (t + 1)) * foldInfoNCEAlpha t := by
      rw [pow_succ]
      ring

private lemma foldInfoNCE_Icc_two_succ_eq_map (n : ℕ) :
    Finset.Icc 2 (n + 1) = (Finset.Icc 1 n).map ⟨Nat.succ, by
      intro a b h
      exact Nat.succ.inj h⟩ := by
  ext q
  simp only [Finset.mem_Icc, Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · intro hq
    refine ⟨q - 1, ?_, by omega⟩
    omega
  · intro hq
    rcases hq with ⟨a, ha, rfl⟩
    omega

/-- Paper label: `cor:fold-infonce-triangular-inversion-collision-spectrum`. -/
theorem paper_fold_infonce_triangular_inversion_collision_spectrum (m Q : Nat) :
    foldInfoNCETriangularInversionCollisionSpectrumStatement m Q := by
  intro n hn
  have htri :
      Omega.OperatorAlgebra.foldInfoNCEFiniteKMomentExpansion m (n + 1) =
        Finset.sum (Finset.Icc 1 n) (fun t =>
          (Nat.choose n t : ℝ) * foldInfoNCEForwardDifferenceCoeff t *
            Omega.OperatorAlgebra.foldCollisionMomentNormalized (t + 1) m) := by
    have hbase := paper_fold_infonce_bayes_infonce_power_sum_expansion m (n + 1)
    rw [foldInfoNCE_Icc_two_succ_eq_map n, Finset.sum_map] at hbase
    refine hbase.trans ?_
    refine Finset.sum_congr rfl ?_
    intro t ht
    change
      (Nat.choose n t : ℝ) * (((-1 : ℝ) ^ (t + 1)) * foldInfoNCEAlpha t) *
          Omega.OperatorAlgebra.foldCollisionMomentNormalized (t + 1) m =
        (Nat.choose n t : ℝ) * foldInfoNCEForwardDifferenceCoeff t *
          Omega.OperatorAlgebra.foldCollisionMomentNormalized (t + 1) m
    rw [foldInfoNCEForwardDifferenceCoeff_eq_alpha]
  refine ⟨htri, foldInfoNCEForwardDifferenceCoeff_eq_alpha n, ?_⟩
  intro hdiag
  let term : ℕ → ℝ := fun t =>
    (Nat.choose n t : ℝ) * foldInfoNCEForwardDifferenceCoeff t *
      Omega.OperatorAlgebra.foldCollisionMomentNormalized (t + 1) m
  have hn' : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hsplit : Finset.sum (Finset.Icc 1 n) term = Finset.sum (Finset.Icc 1 (n - 1)) term + term n := by
    rw [← Finset.insert_Icc_pred_right_eq_Icc (a := 1) (b := n) hn']
    rw [Finset.sum_insert]
    · simp [term, add_comm]
    · simpa [Finset.mem_Icc, hn'] using
        (not_le.mpr (Nat.pred_lt (Nat.ne_of_gt hn')) : ¬ n ≤ n.pred)
  have htri' :
      Omega.OperatorAlgebra.foldInfoNCEFiniteKMomentExpansion m (n + 1) =
        Finset.sum (Finset.Icc 1 (n - 1)) term +
          foldInfoNCEForwardDifferenceCoeff n *
            Omega.OperatorAlgebra.foldCollisionMomentNormalized (n + 1) m := by
    rw [htri, hsplit]
    simp [term, add_comm]
  have hmul :
      Omega.OperatorAlgebra.foldCollisionMomentNormalized (n + 1) m *
          foldInfoNCEForwardDifferenceCoeff n =
        Omega.OperatorAlgebra.foldInfoNCEFiniteKMomentExpansion m (n + 1) -
          Finset.sum (Finset.Icc 1 (n - 1)) term := by
    linarith
  apply (eq_div_iff hdiag).2
  simpa [term, mul_comm, mul_left_comm, mul_assoc] using hmul

end

end Omega.Folding
