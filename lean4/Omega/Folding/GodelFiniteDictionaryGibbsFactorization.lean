import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

namespace Omega.Folding

open scoped BigOperators

/-- The factorial majorant used as the concrete length weight in the finite-dictionary Gibbs
model. -/
noncomputable def foldGodelLengthWeightRaw (B : ℕ) (σ : ℝ) (T : ℕ) : ℝ :=
  (B : ℝ) ^ T / (((T + 1).factorial : ℝ) ^ σ)

/-- The letter weight used by the finite-dictionary Gödel Gibbs model. -/
noncomputable def foldGodelSymbolWeight (B : ℕ) (σ : ℝ) (a : Fin B) : ℝ :=
  ((a.1 + 1 : ℕ) : ℝ) ^ (-σ)

/-- The one-site normalization constant for the finite-dictionary Gödel Gibbs model. -/
noncomputable def foldGodelSymbolPartition (B : ℕ) (σ : ℝ) : ℝ :=
  ∑ a : Fin B, foldGodelSymbolWeight B σ a

/-- The normalized one-site Gibbs marginal. -/
noncomputable def foldGodelSymbolLaw (B : ℕ) (σ : ℝ) (a : Fin B) : ℝ :=
  foldGodelSymbolWeight B σ a / foldGodelSymbolPartition B σ

/-- The length-partition function obtained from the factorial majorant. -/
noncomputable def foldGodelGibbsPartition (B : ℕ) (σ : ℝ) : ℝ :=
  ∑' T : ℕ, foldGodelLengthWeightRaw B σ T

/-- The induced length law. -/
noncomputable def foldGodelLengthLaw (B : ℕ) (σ : ℝ) (T : ℕ) : ℝ :=
  foldGodelLengthWeightRaw B σ T / foldGodelGibbsPartition B σ

/-- For fixed length `T`, the conditional word law is the product of the one-site marginals. -/
noncomputable def foldGodelConditionalLaw (B : ℕ) (σ : ℝ) (T : ℕ) (w : Fin T → Fin B) : ℝ :=
  ∏ t : Fin T, foldGodelSymbolLaw B σ (w t)

/-- The joint law splits into the length law and the conditional product law. -/
noncomputable def foldGodelJointLaw (B : ℕ) (σ : ℝ) (T : ℕ) (w : Fin T → Fin B) : ℝ :=
  foldGodelLengthLaw B σ T * foldGodelConditionalLaw B σ T w

/-- Concrete package for the finite-dictionary Gödel Gibbs factorization:
the factorially normalized length law is summable, the one-site Gibbs marginal is normalized,
and the joint law factors into the length law times the coordinate-product conditional law. -/
def FoldGodelFiniteDictionaryGibbsFactorizationStatement (B : ℕ) (σ : ℝ) : Prop :=
  Summable (foldGodelLengthWeightRaw B σ) ∧
    0 < foldGodelGibbsPartition B σ ∧
    (∑ a : Fin B, foldGodelSymbolLaw B σ a) = 1 ∧
    (∀ T : ℕ, 0 ≤ foldGodelLengthLaw B σ T) ∧
    (∀ T : ℕ, ∀ w : Fin T → Fin B,
      foldGodelConditionalLaw B σ T w = ∏ t : Fin T, foldGodelSymbolLaw B σ (w t)) ∧
    (∀ T : ℕ, ∀ w : Fin T → Fin B,
      foldGodelJointLaw B σ T w =
        foldGodelLengthLaw B σ T * foldGodelConditionalLaw B σ T w)

private lemma foldGodelLengthWeightRaw_pos (B : ℕ) (hB : 1 ≤ B) (σ : ℝ) (T : ℕ) :
    0 < foldGodelLengthWeightRaw B σ T := by
  unfold foldGodelLengthWeightRaw
  have hfac_pos : 0 < (((T + 1).factorial : ℝ) ^ σ) := by
    exact Real.rpow_pos_of_pos (by exact_mod_cast Nat.factorial_pos (T + 1)) σ
  exact div_pos (pow_pos (by exact_mod_cast hB) _) hfac_pos

private lemma foldGodelLengthWeightRaw_nonneg (B : ℕ) (σ : ℝ) (T : ℕ) :
    0 ≤ foldGodelLengthWeightRaw B σ T := by
  unfold foldGodelLengthWeightRaw
  have hfac_pos : 0 < (((T + 1).factorial : ℝ) ^ σ) := by
    exact Real.rpow_pos_of_pos (by exact_mod_cast Nat.factorial_pos (T + 1)) σ
  exact div_nonneg (pow_nonneg (by positivity) _) hfac_pos.le

private lemma foldGodelLengthWeightRaw_ratio (B : ℕ) (hB : 1 ≤ B) (σ : ℝ) (T : ℕ) :
    ‖foldGodelLengthWeightRaw B σ (T + 1)‖ / ‖foldGodelLengthWeightRaw B σ T‖ =
      (B : ℝ) / (((T + 2 : ℕ) : ℝ) ^ σ) := by
  have hT_pos : 0 < foldGodelLengthWeightRaw B σ T :=
    foldGodelLengthWeightRaw_pos B hB σ T
  have hTs_pos : 0 < foldGodelLengthWeightRaw B σ (T + 1) :=
    foldGodelLengthWeightRaw_pos B hB σ (T + 1)
  rw [Real.norm_of_nonneg hTs_pos.le, Real.norm_of_nonneg hT_pos.le]
  unfold foldGodelLengthWeightRaw
  have hfac :
      ((((T + 2).factorial : ℕ) : ℝ) ^ σ) =
        (((T + 2 : ℕ) : ℝ) ^ σ) * ((((T + 1).factorial : ℕ) : ℝ) ^ σ) := by
    calc
      ((((T + 2).factorial : ℕ) : ℝ) ^ σ)
          = ((((T + 2 : ℕ) : ℝ) * ((((T + 1).factorial : ℕ) : ℝ)) ^ 1) ^ σ) := by
              rw [Nat.factorial_succ, Nat.cast_mul]
              ring_nf
      _ = ((((T + 2 : ℕ) : ℝ) * ((((T + 1).factorial : ℕ) : ℝ))) ^ σ) := by simp
      _ = (((T + 2 : ℕ) : ℝ) ^ σ) * ((((T + 1).factorial : ℕ) : ℝ) ^ σ) := by
            rw [Real.mul_rpow] <;> positivity
  have hstep_ne : (((T + 2 : ℕ) : ℝ) ^ σ) ≠ 0 := by
    exact (Real.rpow_pos_of_pos (by positivity) σ).ne'
  have hfac_ne : ((((T + 1).factorial : ℕ) : ℝ) ^ σ) ≠ 0 := by
    exact (Real.rpow_pos_of_pos (by exact_mod_cast Nat.factorial_pos (T + 1)) σ).ne'
  rw [hfac, pow_succ]
  field_simp [hstep_ne, hfac_ne]

private theorem foldGodelLengthWeightRaw_summable (B : ℕ) (hB : 1 ≤ B) (σ : ℝ) (hσ : 0 < σ) :
    Summable (foldGodelLengthWeightRaw B σ) := by
  have hpow :
      Filter.Tendsto (fun T : ℕ => (((T + 2 : ℕ) : ℝ) ^ σ)) Filter.atTop Filter.atTop := by
    have hshift_nat : Filter.Tendsto (fun T : ℕ => T + 2) Filter.atTop Filter.atTop := by
      simpa using (Filter.tendsto_add_atTop_iff_nat 2).2 Filter.tendsto_id
    have hshift : Filter.Tendsto (fun T : ℕ => ((T + 2 : ℕ) : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop.comp hshift_nat
    simpa [Nat.cast_add] using (tendsto_rpow_atTop hσ).comp hshift
  have hratio :
      Filter.Tendsto
        (fun T ↦ ‖foldGodelLengthWeightRaw B σ (T + 1)‖ / ‖foldGodelLengthWeightRaw B σ T‖)
        Filter.atTop (nhds 0) := by
    refine Filter.Tendsto.congr'
      (Filter.Eventually.of_forall fun T => (foldGodelLengthWeightRaw_ratio B hB σ T).symm) ?_
    simpa using Filter.Tendsto.const_div_atTop hpow (B : ℝ)
  have hne :
      ∀ᶠ T in Filter.atTop, foldGodelLengthWeightRaw B σ T ≠ 0 := by
    exact Filter.Eventually.of_forall fun T =>
      (foldGodelLengthWeightRaw_pos B hB σ T).ne'
  exact summable_of_ratio_test_tendsto_lt_one zero_lt_one hne hratio

private lemma foldGodelSymbolWeight_pos (B : ℕ) (σ : ℝ) (a : Fin B) :
    0 < foldGodelSymbolWeight B σ a := by
  unfold foldGodelSymbolWeight
  exact Real.rpow_pos_of_pos (by positivity) (-σ)

private lemma foldGodelSymbolPartition_pos (B : ℕ) (σ : ℝ) (hB : 1 ≤ B) :
    0 < foldGodelSymbolPartition B σ := by
  have hmem : (⟨0, hB⟩ : Fin B) ∈ Finset.univ := by simp
  have hle :
      foldGodelSymbolWeight B σ ⟨0, hB⟩ ≤ foldGodelSymbolPartition B σ := by
    unfold foldGodelSymbolPartition
    exact Finset.single_le_sum
      (fun a _ => (foldGodelSymbolWeight_pos B σ a).le) hmem
  exact lt_of_lt_of_le (foldGodelSymbolWeight_pos B σ ⟨0, hB⟩) hle

/-- Paper label: `thm:fold-godel-finite-dictionary-gibbs-factorization`.
The factorially summable length weights from the holomorphic Dirichlet wrapper normalize to a
length law, the fixed-length conditional law is the product of the one-site Gibbs marginals, and
the resulting joint law factors accordingly. -/
theorem paper_fold_godel_finite_dictionary_gibbs_factorization (B : Nat) (sigma : ℝ)
    (hB : 1 <= B) (hsigma : 0 < sigma) : FoldGodelFiniteDictionaryGibbsFactorizationStatement B sigma := by
  have hsummable :
      Summable (foldGodelLengthWeightRaw B sigma) :=
    foldGodelLengthWeightRaw_summable B hB sigma hsigma
  have hterm0 : 0 < foldGodelLengthWeightRaw B sigma 0 := by
    simp [foldGodelLengthWeightRaw]
  have hpartition_pos : 0 < foldGodelGibbsPartition B sigma := by
    unfold foldGodelGibbsPartition
    exact hsummable.tsum_pos (foldGodelLengthWeightRaw_nonneg B sigma) 0 hterm0
  have hsymbol_pos : 0 < foldGodelSymbolPartition B sigma :=
    foldGodelSymbolPartition_pos B sigma hB
  have hsymbol_sum : (∑ a : Fin B, foldGodelSymbolLaw B sigma a) = 1 := by
    unfold foldGodelSymbolLaw foldGodelSymbolPartition
    calc
      (∑ a : Fin B, foldGodelSymbolWeight B sigma a / ∑ a : Fin B, foldGodelSymbolWeight B sigma a) =
          (∑ a : Fin B, foldGodelSymbolWeight B sigma a) /
            ∑ a : Fin B, foldGodelSymbolWeight B sigma a := by
              rw [← Finset.sum_div]
      _ = 1 := by
        exact div_self hsymbol_pos.ne'
  refine ⟨hsummable, hpartition_pos, hsymbol_sum, ?_, ?_, ?_⟩
  · intro T
    unfold foldGodelLengthLaw
    exact div_nonneg (foldGodelLengthWeightRaw_nonneg B sigma T) hpartition_pos.le
  · intro T w
    rfl
  · intro T w
    rfl

end Omega.Folding
