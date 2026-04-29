import Mathlib
import Omega.Conclusion.SemanticEquivalenceUndecidable

open Filter Topology

namespace Omega.Folding

open Omega.Conclusion

noncomputable section

/-- The normalized loss contributed by the constant-map branch of the halting reduction. -/
def fold_infonce_rate_undecidable_constant_map_normalized_loss : ℝ :=
  Real.log 2

/-- The dyadic upper envelope coming from the identity-map branch and the bound
`0 ≤ log (1 + J) ≤ J`. -/
def fold_infonce_rate_undecidable_identity_map_normalized_loss (m : ℕ) : ℝ :=
  ((1 / 2 : ℝ) ^ m)

/-- The machine-indexed normalized-loss family: before halting it stays on the constant-map
branch, and after halting it switches permanently to the identity-map branch. -/
def fold_infonce_rate_undecidable_normalized_loss
    (haltsWithin : ℕ → ℕ → Prop) (e m : ℕ) : ℝ :=
  by
    classical
    exact
      if haltsWithin e m then
        fold_infonce_rate_undecidable_identity_map_normalized_loss m
      else
        fold_infonce_rate_undecidable_constant_map_normalized_loss

/-- The vanishing-rate property appearing in the paper statement. -/
def fold_infonce_rate_undecidable_zero_rate (loss : ℕ → ℝ) : Prop :=
  Tendsto loss atTop (𝓝 0)

/-- Concrete undecidability wrapper for the halting-to-InfoNCE-rate reduction. -/
def fold_infonce_rate_undecidable_statement : Prop :=
  ∀ (haltsWithin : ℕ → ℕ → Prop) (halts : ℕ → Prop),
    RelationPointwiseDecidable haltsWithin →
    (∀ e, halts e ↔ ∃ N, haltsWithin e N) →
    (∀ e N M, haltsWithin e N → N ≤ M → haltsWithin e M) →
    ¬ PredicatePointwiseDecidable halts →
    ¬ PredicatePointwiseDecidable fun e =>
      fold_infonce_rate_undecidable_zero_rate
        (fun m => fold_infonce_rate_undecidable_normalized_loss haltsWithin e m)

lemma fold_infonce_rate_undecidable_zero_rate_of_halts
    {haltsWithin : ℕ → ℕ → Prop} {halts : ℕ → Prop}
    (hHalts : ∀ e, halts e ↔ ∃ N, haltsWithin e N)
    (hMono : ∀ e N M, haltsWithin e N → N ≤ M → haltsWithin e M)
    {e : ℕ} (hh : halts e) :
    fold_infonce_rate_undecidable_zero_rate
      (fun m => fold_infonce_rate_undecidable_normalized_loss haltsWithin e m) := by
  rcases (hHalts e).1 hh with ⟨N, hN⟩
  have hEventually :
      (fun m => fold_infonce_rate_undecidable_normalized_loss haltsWithin e m) =ᶠ[atTop]
        fun m => fold_infonce_rate_undecidable_identity_map_normalized_loss m := by
    filter_upwards [Filter.eventually_ge_atTop N] with m hm
    have hm' : haltsWithin e m := hMono e N m hN hm
    simpa [fold_infonce_rate_undecidable_normalized_loss, hm'] using rfl
  have hPow :
      Tendsto (fun m : ℕ => fold_infonce_rate_undecidable_identity_map_normalized_loss m) atTop
        (𝓝 0) := by
    unfold fold_infonce_rate_undecidable_identity_map_normalized_loss
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
  exact Tendsto.congr' hEventually.symm hPow

lemma fold_infonce_rate_undecidable_not_zero_rate_of_not_halting
    {haltsWithin : ℕ → ℕ → Prop} {halts : ℕ → Prop}
    (hHalts : ∀ e, halts e ↔ ∃ N, haltsWithin e N)
    {e : ℕ} (hh : ¬ halts e) :
    ¬ fold_infonce_rate_undecidable_zero_rate
      (fun m => fold_infonce_rate_undecidable_normalized_loss haltsWithin e m) := by
  intro hZero
  have hconst :
      Tendsto (fun m => fold_infonce_rate_undecidable_normalized_loss haltsWithin e m) atTop
        (𝓝 fold_infonce_rate_undecidable_constant_map_normalized_loss) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    refine Filter.Eventually.of_forall ?_
    intro m
    have hm : ¬ haltsWithin e m := by
      intro hm
      exact hh ((hHalts e).2 ⟨m, hm⟩)
    simpa [fold_infonce_rate_undecidable_normalized_loss, hm] using rfl
  have hEq :
      fold_infonce_rate_undecidable_constant_map_normalized_loss = 0 :=
    tendsto_nhds_unique hconst hZero
  have hlog2 : 0 < fold_infonce_rate_undecidable_constant_map_normalized_loss := by
    unfold fold_infonce_rate_undecidable_constant_map_normalized_loss
    exact Real.log_pos (by norm_num)
  exact (ne_of_gt hlog2) hEq

/-- Paper label: `thm:fold-infonce-rate-undecidable`. -/
theorem paper_fold_infonce_rate_undecidable :
    fold_infonce_rate_undecidable_statement := by
  intro haltsWithin halts _hStepDec hHalts hMono hUndecidable hRateDec
  rcases hRateDec with ⟨hRateDecidable⟩
  apply hUndecidable
  refine ⟨fun e => ?_⟩
  letI := hRateDecidable e
  have hReduction :
      halts e ↔
        fold_infonce_rate_undecidable_zero_rate
          (fun m => fold_infonce_rate_undecidable_normalized_loss haltsWithin e m) := by
    constructor
    · intro hh
      exact fold_infonce_rate_undecidable_zero_rate_of_halts hHalts hMono hh
    · intro hZero
      by_contra hh
      exact (fold_infonce_rate_undecidable_not_zero_rate_of_not_halting hHalts hh) hZero
  exact decidable_of_iff
    (fold_infonce_rate_undecidable_zero_rate
      (fun m => fold_infonce_rate_undecidable_normalized_loss haltsWithin e m))
    hReduction.symm

end

end Omega.Folding
