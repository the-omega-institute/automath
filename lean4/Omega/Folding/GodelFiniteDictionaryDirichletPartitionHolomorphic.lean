import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

namespace Omega.Folding

/-- The factorial majorant controlling the length-`T` layer in the finite-dictionary Gödel
Dirichlet partition. -/
noncomputable def foldGodelDirichletLayerMajorant (B : ℕ) (σ : ℝ) (T : ℕ) : ℝ :=
  (B : ℝ) ^ T / (((T + 1).factorial : ℝ) ^ σ)

/-- Concrete M-test package for the finite-dictionary Gödel Dirichlet partition: every positive
real part `σ` admits the factorially dominated layer majorant required for absolute convergence on
the open right half-plane. -/
def FoldGodelFiniteDictionaryDirichletPartitionHolomorphicStatement (B : ℕ) : Prop :=
  ∀ ⦃σ : ℝ⦄, 0 < σ → Summable (foldGodelDirichletLayerMajorant B σ)

private lemma foldGodelDirichletLayerMajorant_pos (B : ℕ) (hB : 1 ≤ B) (σ : ℝ) (T : ℕ) :
    0 < foldGodelDirichletLayerMajorant B σ T := by
  unfold foldGodelDirichletLayerMajorant
  have hB' : 0 < (B : ℝ) := by
    exact_mod_cast hB
  have hfac : 0 < (((T + 1).factorial : ℝ) ^ σ) := by
    exact Real.rpow_pos_of_pos (by exact_mod_cast Nat.factorial_pos (T + 1)) σ
  exact div_pos (pow_pos hB' _) hfac

private lemma foldGodelDirichletLayerMajorant_ratio (B : ℕ) (hB : 1 ≤ B) (σ : ℝ) (T : ℕ) :
    ‖foldGodelDirichletLayerMajorant B σ (T + 1)‖ / ‖foldGodelDirichletLayerMajorant B σ T‖ =
      (B : ℝ) / (((T + 2 : ℕ) : ℝ) ^ σ) := by
  have hT_pos : 0 < foldGodelDirichletLayerMajorant B σ T :=
    foldGodelDirichletLayerMajorant_pos B hB σ T
  have hTs_pos : 0 < foldGodelDirichletLayerMajorant B σ (T + 1) :=
    foldGodelDirichletLayerMajorant_pos B hB σ (T + 1)
  rw [Real.norm_of_nonneg hTs_pos.le, Real.norm_of_nonneg hT_pos.le]
  unfold foldGodelDirichletLayerMajorant
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

/-- Paper label: `thm:fold-godel-finite-dictionary-dirichlet-partition-holomorphic`.
The factorial majorant `B^T / ((T + 1)!)^σ` is summable for every `σ > 0`, which is the concrete
Weierstrass M-test input used for the right-half-plane holomorphy argument. -/
theorem paper_fold_godel_finite_dictionary_dirichlet_partition_holomorphic (B : Nat)
    (hB : 1 <= B) : FoldGodelFiniteDictionaryDirichletPartitionHolomorphicStatement B := by
  intro σ hσ
  have hpow :
      Filter.Tendsto (fun T : ℕ => (((T + 2 : ℕ) : ℝ) ^ σ)) Filter.atTop Filter.atTop := by
    have hshift_nat : Filter.Tendsto (fun T : ℕ => T + 2) Filter.atTop Filter.atTop := by
      simpa using (Filter.tendsto_add_atTop_iff_nat 2).2 Filter.tendsto_id
    have hshift : Filter.Tendsto (fun T : ℕ => ((T + 2 : ℕ) : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop.comp hshift_nat
    simpa [Nat.cast_add] using (tendsto_rpow_atTop hσ).comp hshift
  have hratio :
      Filter.Tendsto
        (fun T ↦ ‖foldGodelDirichletLayerMajorant B σ (T + 1)‖ /
            ‖foldGodelDirichletLayerMajorant B σ T‖)
        Filter.atTop (nhds 0) := by
    refine Filter.Tendsto.congr'
      (Filter.Eventually.of_forall fun T => (foldGodelDirichletLayerMajorant_ratio B hB σ T).symm) ?_
    simpa using Filter.Tendsto.const_div_atTop hpow (B : ℝ)
  have hne :
      ∀ᶠ T in Filter.atTop, foldGodelDirichletLayerMajorant B σ T ≠ 0 := by
    exact Filter.Eventually.of_forall fun T =>
      (foldGodelDirichletLayerMajorant_pos B hB σ T).ne'
  exact summable_of_ratio_test_tendsto_lt_one zero_lt_one hne hratio

end Omega.Folding
