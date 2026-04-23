import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Conclusion.SmithNormalizedKernelPositiveFiniteEulerCorrection

namespace Omega.Conclusion

noncomputable section

/-- The finite bad-prime correction evaluated at the residue point `X = 1 / p`. -/
def conclusion_smith_normalized_kernel_average_order_local_factor
    (p : ℕ) (profile : List ℕ) (cut : ℕ) : ℝ :=
  1 + Finset.sum (Finset.Icc 1 cut) fun k =>
    (smithLocalCoeff p profile k : ℝ) / (p : ℝ) ^ k

/-- The positive residue constant predicted by the normalized-kernel Euler correction. -/
def conclusion_smith_normalized_kernel_average_order_constant
    (S : Finset ℕ) (profile : ℕ → List ℕ) (cut : ℕ → ℕ) : ℝ :=
  Finset.prod S fun p =>
    conclusion_smith_normalized_kernel_average_order_local_factor p (profile p) (cut p)

/-- Paper-facing average-order wrapper for the Smith normalized-kernel Euler package: the
bad-prime residue constant is positive and equals `1` exactly in the trivial Smith case. -/
def conclusion_smith_normalized_kernel_average_order_statement : Prop :=
  ∀ (S : Finset ℕ) (profile : ℕ → List ℕ) (cut : ℕ → ℕ)
    (hcut : ∀ p i, i ∈ profile p → i ≤ cut p)
    (hjump :
      ∀ p k, 1 ≤ k → k ≤ cut p → smithPartialSum (profile p) (k - 1) < smithPartialSum (profile p) k)
    (hprime : ∀ p ∈ S, 2 ≤ p)
    (hcutpos : ∀ p ∈ S, 1 ≤ cut p),
    smithEulerFactorization S profile cut ∧
      0 < conclusion_smith_normalized_kernel_average_order_constant S profile cut ∧
      (conclusion_smith_normalized_kernel_average_order_constant S profile cut = 1 ↔ S = ∅)

lemma conclusion_smith_normalized_kernel_average_order_local_factor_gt_one
    {S : Finset ℕ} {profile : ℕ → List ℕ} {cut : ℕ → ℕ}
    (hlocal : smithLocalCorrectionPositive S profile cut)
    (hprime : ∀ p ∈ S, 2 ≤ p)
    {p : ℕ} (hp : p ∈ S) (hcutpos : 1 ≤ cut p) :
    1 < conclusion_smith_normalized_kernel_average_order_local_factor p (profile p) (cut p) := by
  unfold conclusion_smith_normalized_kernel_average_order_local_factor
  have hmem : 1 ∈ Finset.Icc 1 (cut p) := by simp [hcutpos]
  have hp_nat : 0 < p := lt_of_lt_of_le (by omega) (hprime p hp)
  have hp_real : 0 < (p : ℝ) := by exact_mod_cast hp_nat
  have hterm_pos : 0 < (smithLocalCoeff p (profile p) 1 : ℝ) / (p : ℝ) ^ 1 := by
    have hcoeff_nat : 0 < smithLocalCoeff p (profile p) 1 := hlocal p hp 1 le_rfl hcutpos
    have hcoeff_real : 0 < (smithLocalCoeff p (profile p) 1 : ℝ) := by exact_mod_cast hcoeff_nat
    have hpow : 0 < (p : ℝ) ^ 1 := by simpa using pow_pos hp_real 1
    exact div_pos hcoeff_real hpow
  have hsum_pos :
      0 < Finset.sum (Finset.Icc 1 (cut p)) (fun k =>
        (smithLocalCoeff p (profile p) k : ℝ) / (p : ℝ) ^ k) := by
    refine Finset.sum_pos ?_ ?_
    · intro k hk
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hkcut : k ≤ cut p := (Finset.mem_Icc.mp hk).2
      have hcoeff_nat : 0 < smithLocalCoeff p (profile p) k := hlocal p hp k hk1 hkcut
      have hcoeff_real : 0 < (smithLocalCoeff p (profile p) k : ℝ) := by exact_mod_cast hcoeff_nat
      have hpow : 0 < (p : ℝ) ^ k := pow_pos hp_real k
      exact div_pos hcoeff_real hpow
    · exact ⟨1, hmem⟩
  simpa using add_lt_add_left hsum_pos 1

lemma conclusion_smith_normalized_kernel_average_order_constant_pos
    {S : Finset ℕ} {profile : ℕ → List ℕ} {cut : ℕ → ℕ}
    (hlocal : smithLocalCorrectionPositive S profile cut)
    (hprime : ∀ p ∈ S, 2 ≤ p)
    (hcutpos : ∀ p ∈ S, 1 ≤ cut p) :
    0 < conclusion_smith_normalized_kernel_average_order_constant S profile cut := by
  unfold conclusion_smith_normalized_kernel_average_order_constant
  refine Finset.prod_pos ?_
  intro p hp
  exact lt_trans zero_lt_one
    (conclusion_smith_normalized_kernel_average_order_local_factor_gt_one hlocal hprime hp (hcutpos p hp))

lemma conclusion_smith_normalized_kernel_average_order_constant_gt_one_of_nonempty
    {S : Finset ℕ} {profile : ℕ → List ℕ} {cut : ℕ → ℕ}
    (hlocal : smithLocalCorrectionPositive S profile cut)
    (hprime : ∀ p ∈ S, 2 ≤ p)
    (hcutpos : ∀ p ∈ S, 1 ≤ cut p)
    (hS : S.Nonempty) :
    1 < conclusion_smith_normalized_kernel_average_order_constant S profile cut := by
  rcases hS with ⟨p, hp⟩
  have hp_gt :
      1 < conclusion_smith_normalized_kernel_average_order_local_factor p (profile p) (cut p) :=
    conclusion_smith_normalized_kernel_average_order_local_factor_gt_one hlocal hprime hp (hcutpos p hp)
  have hrest_ge_one :
      1 ≤ Finset.prod (S.erase p) fun q =>
        conclusion_smith_normalized_kernel_average_order_local_factor q (profile q) (cut q) := by
    classical
    have hprod_ge_one :
        ∀ U : Finset ℕ,
          (∀ q ∈ U, q ∈ S) →
            1 ≤ Finset.prod U fun q =>
              conclusion_smith_normalized_kernel_average_order_local_factor q (profile q) (cut q) := by
      intro U hU
      induction U using Finset.induction_on with
      | empty =>
          simp
      | @insert q T hqT ih =>
          rw [Finset.prod_insert hqT]
          have hqS : q ∈ S := hU q (by simp)
          have hT : ∀ r ∈ T, r ∈ S := by
            intro r hr
            exact hU r (by simp [hr])
          have hq_ge :
              1 ≤ conclusion_smith_normalized_kernel_average_order_local_factor q (profile q) (cut q) := by
            exact (conclusion_smith_normalized_kernel_average_order_local_factor_gt_one
              hlocal hprime hqS (hcutpos q hqS)).le
          have hT_ge :
              1 ≤ Finset.prod T fun q =>
                conclusion_smith_normalized_kernel_average_order_local_factor q (profile q) (cut q) := ih hT
          have hq_nonneg :
              0 ≤ conclusion_smith_normalized_kernel_average_order_local_factor q (profile q) (cut q) :=
            le_trans (show (0 : ℝ) ≤ 1 by norm_num) hq_ge
          calc
            1 = 1 * 1 := by ring
            _ ≤ conclusion_smith_normalized_kernel_average_order_local_factor q (profile q) (cut q) *
                  Finset.prod T fun q =>
                    conclusion_smith_normalized_kernel_average_order_local_factor q (profile q) (cut q) := by
                  exact mul_le_mul hq_ge hT_ge (by norm_num : (0 : ℝ) ≤ 1) hq_nonneg
    exact hprod_ge_one (S.erase p) (fun q hq => Finset.mem_of_mem_erase hq)
  have hwhole :
      1 <
        conclusion_smith_normalized_kernel_average_order_local_factor p (profile p) (cut p) *
          Finset.prod (S.erase p) fun q =>
            conclusion_smith_normalized_kernel_average_order_local_factor q (profile q) (cut q) := by
    have hp_pos :
        0 <
          conclusion_smith_normalized_kernel_average_order_local_factor p (profile p) (cut p) :=
      lt_trans zero_lt_one hp_gt
    calc
      1 < conclusion_smith_normalized_kernel_average_order_local_factor p (profile p) (cut p) := hp_gt
      _ = conclusion_smith_normalized_kernel_average_order_local_factor p (profile p) (cut p) * 1 := by ring
      _ ≤ conclusion_smith_normalized_kernel_average_order_local_factor p (profile p) (cut p) *
            Finset.prod (S.erase p) fun q =>
              conclusion_smith_normalized_kernel_average_order_local_factor q (profile q) (cut q) := by
            exact mul_le_mul_of_nonneg_left hrest_ge_one hp_pos.le
  unfold conclusion_smith_normalized_kernel_average_order_constant
  rw [← Finset.insert_erase hp, Finset.prod_insert (Finset.notMem_erase p S)]
  exact hwhole

/-- Paper label: `cor:conclusion-smith-normalized-kernel-average-order`. -/
theorem paper_conclusion_smith_normalized_kernel_average_order :
    conclusion_smith_normalized_kernel_average_order_statement := by
  intro S profile cut hcut hjump hprime hcutpos
  have hpackage :=
    paper_conclusion_smith_normalized_kernel_positive_finite_euler_correction
      S profile cut hcut hjump hprime
  rcases hpackage with ⟨hEuler, hlocal, _hPole⟩
  refine ⟨hEuler, conclusion_smith_normalized_kernel_average_order_constant_pos hlocal hprime hcutpos, ?_⟩
  constructor
  · intro hconst
    by_contra hS
    have hgt :
        1 < conclusion_smith_normalized_kernel_average_order_constant S profile cut :=
      conclusion_smith_normalized_kernel_average_order_constant_gt_one_of_nonempty
        hlocal hprime hcutpos (Finset.nonempty_iff_ne_empty.mpr hS)
    exact (ne_of_gt hgt) hconst
  · intro hS
    subst hS
    simp [conclusion_smith_normalized_kernel_average_order_constant]

end

end Omega.Conclusion
