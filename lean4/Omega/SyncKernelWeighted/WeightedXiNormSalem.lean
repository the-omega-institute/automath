import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.SyncKernelWeighted.WeightedXiSingleExceptionPair

namespace Omega.SyncKernelWeighted

noncomputable section

/-- The Galois-conjugate sextic numerator under `√3 ↦ -√3`. -/
def sync_kernel_weighted_xi_norm_salem_conj_N (r : ℝ) : ℝ :=
  -(Real.sqrt 3) * r ^ 6 - 2 * r ^ 5 + 3 * Real.sqrt 3 * r ^ 4 - 8 * r ^ 3 +
    3 * Real.sqrt 3 * r ^ 2 - 2 * r - Real.sqrt 3

/-- The norm polynomial `F(r) = -Nm(N)(r)`. -/
def sync_kernel_weighted_xi_norm_salem_F (r : ℝ) : ℝ :=
  -sync_kernel_weighted_xi_single_exception_pair_N r *
    sync_kernel_weighted_xi_norm_salem_conj_N r

/-- The Salem-type sextic in the variable `y = r²`. -/
def sync_kernel_weighted_xi_norm_salem_f (y : ℝ) : ℝ :=
  3 * y ^ 6 - 22 * y ^ 5 - 23 * y ^ 4 - 12 * y ^ 3 - 23 * y ^ 2 - 22 * y + 3

/-- The mod-`7` reduction of the Salem sextic. -/
def sync_kernel_weighted_xi_norm_salem_mod7 (y : ZMod 7) : ZMod 7 :=
  3 * y ^ 6 + 6 * y ^ 5 + 5 * y ^ 4 + 2 * y ^ 3 + 5 * y ^ 2 + 6 * y + 3

/-- The finite-field root-freeness witness used for the appendix-local irreducibility audit. -/
def sync_kernel_weighted_xi_norm_salem_mod7_root_free : Prop :=
  ∀ y : ZMod 7, sync_kernel_weighted_xi_norm_salem_mod7 y ≠ 0

private lemma sync_kernel_weighted_xi_norm_salem_F_formula (r : ℝ) :
    sync_kernel_weighted_xi_norm_salem_F r =
      3 * r ^ 12 - 22 * r ^ 10 - 23 * r ^ 8 - 12 * r ^ 6 - 23 * r ^ 4 - 22 * r ^ 2 + 3 := by
  unfold sync_kernel_weighted_xi_norm_salem_F sync_kernel_weighted_xi_single_exception_pair_N
    sync_kernel_weighted_xi_norm_salem_conj_N
  ring_nf
  have hsqrt3_sq : (Real.sqrt 3 : ℝ) ^ 2 = 3 := by
    have h : (Real.sqrt 3 : ℝ) ^ 2 = 3 := by
      simpa using Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    exact h
  rw [hsqrt3_sq]
  ring

private lemma sync_kernel_weighted_xi_norm_salem_F_eq_f_sq (r : ℝ) :
    sync_kernel_weighted_xi_norm_salem_F r = sync_kernel_weighted_xi_norm_salem_f (r ^ 2) := by
  rw [sync_kernel_weighted_xi_norm_salem_F_formula]
  unfold sync_kernel_weighted_xi_norm_salem_f
  ring

private lemma sync_kernel_weighted_xi_norm_salem_mod7_root_free_true :
    sync_kernel_weighted_xi_norm_salem_mod7_root_free := by
  intro y
  fin_cases y <;> decide

/-- Paper label: `prop:sync-kernel-weighted-xi-norm-salem`.
Expanding the norm of the completed sextic numerator produces the explicit degree-`12` polynomial
`F(r)`, which descends to the Salem-type sextic `f(y)` under `y = r²`. The existing
single-exception-pair theorem supplies the exceptional real root `α > 1`, hence the reciprocal
Salem pair `α², α⁻²`, and the mod-`7` reduction is root-free as the local finite-field witness. -/
theorem paper_sync_kernel_weighted_xi_norm_salem :
    (∀ r : ℝ,
      sync_kernel_weighted_xi_norm_salem_F r =
        3 * r ^ 12 - 22 * r ^ 10 - 23 * r ^ 8 - 12 * r ^ 6 - 23 * r ^ 4 - 22 * r ^ 2 + 3) ∧
    (∀ r : ℝ,
      sync_kernel_weighted_xi_norm_salem_F r =
        sync_kernel_weighted_xi_norm_salem_f (r ^ 2)) ∧
    ∃ α : ℝ,
      1 < α ∧
      sync_kernel_weighted_xi_norm_salem_f (α ^ 2) = 0 ∧
      sync_kernel_weighted_xi_norm_salem_f ((α⁻¹) ^ 2) = 0 ∧
      sync_kernel_weighted_xi_norm_salem_mod7_root_free := by
  rcases paper_sync_kernel_weighted_xi_single_exception_pair with
    ⟨_, _, _, _, _, _, t3, α, _, _, _, _, _, _, ht3lo, ht3hi, hPt3, hα, hαgt1, _, _, hNα, hNαinv⟩
  have hFα : sync_kernel_weighted_xi_norm_salem_F α = 0 := by
    unfold sync_kernel_weighted_xi_norm_salem_F
    rw [hNα]
    ring
  have hFinv : sync_kernel_weighted_xi_norm_salem_F α⁻¹ = 0 := by
    unfold sync_kernel_weighted_xi_norm_salem_F
    rw [hNαinv]
    ring
  have hfα : sync_kernel_weighted_xi_norm_salem_f (α ^ 2) = 0 := by
    rw [← sync_kernel_weighted_xi_norm_salem_F_eq_f_sq α]
    exact hFα
  have hfinv : sync_kernel_weighted_xi_norm_salem_f ((α⁻¹) ^ 2) = 0 := by
    rw [← sync_kernel_weighted_xi_norm_salem_F_eq_f_sq α⁻¹]
    exact hFinv
  refine ⟨sync_kernel_weighted_xi_norm_salem_F_formula, sync_kernel_weighted_xi_norm_salem_F_eq_f_sq,
    α, ?_, hfα, hfinv, sync_kernel_weighted_xi_norm_salem_mod7_root_free_true⟩
  simpa [hα] using hαgt1

end
end Omega.SyncKernelWeighted
