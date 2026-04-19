import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open scoped BigOperators

noncomputable section

/-- The pointwise Möbius--Abel truncation majorant used in the real-input-40 appendix. -/
def realInput40LogMTruncTerm (A lam : ℝ) (K n : ℕ) : ℝ :=
  A * (lam⁻¹) ^ (K + 1 + n) / (K + 1 + n)

/-- Replacing `1 / (K + 1 + n)` by the uniform cutoff `1 / (K + 1)` yields the geometric
comparison series. -/
def realInput40LogMTruncMajorant (A lam : ℝ) (K n : ℕ) : ℝ :=
  A * (lam⁻¹) ^ (K + 1 + n) / (K + 1)

/-- The geometric-tail bound before rewriting `1 - λ⁻¹` in the paper's `λ - 1` form. -/
def realInput40LogMTruncGeomBound (A lam : ℝ) (K : ℕ) : ℝ :=
  A / (K + 1) * (lam⁻¹) ^ (K + 1) * (1 - lam⁻¹)⁻¹

/-- The explicit `λ`-form tail bound appearing in the appendix proof. -/
def realInput40LogMTruncClosedBound (A lam : ℝ) (K : ℕ) : ℝ :=
  A * (lam⁻¹) ^ K / ((K + 1) * (lam - 1))

/-- The Möbius--Abel truncation bound for the real-input-40 finite-part constant: each tail term
is dominated by `A * λ^(-m) / m`, the resulting series is bounded by a geometric comparison, and
the geometric form rewrites to the closed bound used in the paper.
    prop:real-input-40-logM-trunc-bound -/
theorem paper_real_input_40_logM_trunc_bound
    (A lam : ℝ) (K : ℕ) (hA : 0 ≤ A) (hlam : 1 < lam) :
    (∀ n, realInput40LogMTruncTerm A lam K n ≤ realInput40LogMTruncMajorant A lam K n) ∧
      (∑' n, realInput40LogMTruncTerm A lam K n) ≤ realInput40LogMTruncGeomBound A lam K ∧
      realInput40LogMTruncGeomBound A lam K = realInput40LogMTruncClosedBound A lam K := by
  have hlam0 : 0 < lam := lt_trans zero_lt_one hlam
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam0
  have hr0 : 0 ≤ lam⁻¹ := by positivity
  have hr1 : lam⁻¹ < 1 := by
    simpa using inv_lt_one_of_one_lt₀ hlam
  have hterm :
      ∀ n, realInput40LogMTruncTerm A lam K n ≤ realInput40LogMTruncMajorant A lam K n := by
    intro n
    have hcutoff :
        (1 : ℝ) / (K + 1 + n : ℝ) ≤ (1 : ℝ) / (K + 1 : ℝ) := by
      have hk : (0 : ℝ) < K + 1 := by positivity
      have hmono : (K + 1 : ℝ) ≤ K + 1 + n := by
        exact_mod_cast Nat.le_add_right (K + 1) n
      exact one_div_le_one_div_of_le hk hmono
    have hscale : 0 ≤ A * (lam⁻¹) ^ (K + 1 + n) := by positivity
    simpa [realInput40LogMTruncTerm, realInput40LogMTruncMajorant, div_eq_mul_inv, mul_assoc,
      mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_left hcutoff hscale
  have hmajorant_summable : Summable (fun n ↦ realInput40LogMTruncMajorant A lam K n) := by
    have hgeom : Summable (fun n : ℕ ↦ (lam⁻¹) ^ n) := summable_geometric_of_lt_one hr0 hr1
    convert hgeom.mul_left (A / (K + 1) * (lam⁻¹) ^ (K + 1)) using 1
    ext n
    rw [realInput40LogMTruncMajorant, pow_add]
    ring
  have hterm_nonneg : ∀ n, 0 ≤ realInput40LogMTruncTerm A lam K n := by
    intro n
    exact div_nonneg (mul_nonneg hA (pow_nonneg hr0 _)) (by positivity)
  have hterm_summable : Summable (fun n ↦ realInput40LogMTruncTerm A lam K n) :=
    Summable.of_nonneg_of_le hterm_nonneg hterm hmajorant_summable
  have hmajorant_tsum :
      (∑' n, realInput40LogMTruncMajorant A lam K n) = realInput40LogMTruncGeomBound A lam K := by
    calc
      (∑' n, realInput40LogMTruncMajorant A lam K n)
          = ∑' n, (A / (K + 1) * (lam⁻¹) ^ (K + 1)) * (lam⁻¹) ^ n := by
              congr with n
              rw [realInput40LogMTruncMajorant, pow_add]
              ring
      _ = (A / (K + 1) * (lam⁻¹) ^ (K + 1)) * ∑' n, (lam⁻¹) ^ n := by rw [tsum_mul_left]
      _ = realInput40LogMTruncGeomBound A lam K := by
            rw [tsum_geometric_of_lt_one hr0 hr1, realInput40LogMTruncGeomBound]
  have htsum_le :
      (∑' n, realInput40LogMTruncTerm A lam K n) ≤ ∑' n, realInput40LogMTruncMajorant A lam K n :=
    Summable.tsum_le_tsum hterm hterm_summable hmajorant_summable
  refine ⟨hterm, htsum_le.trans_eq hmajorant_tsum, ?_⟩
  have hk_ne : (K + 1 : ℝ) ≠ 0 := by positivity
  have hlam1_ne : lam - 1 ≠ 0 := sub_ne_zero.mpr hlam.ne'
  have hinv :
      (1 - lam⁻¹)⁻¹ = lam / (lam - 1) := by
    field_simp [hlam_ne, hlam1_ne]
  have hcancel :
      lam⁻¹ * (lam / (lam - 1)) = (lam - 1)⁻¹ := by
    field_simp [hlam_ne, hlam1_ne]
  calc
    realInput40LogMTruncGeomBound A lam K
        = A / (K + 1) * ((lam⁻¹) ^ K * lam⁻¹) * (lam / (lam - 1)) := by
            rw [realInput40LogMTruncGeomBound, pow_succ, hinv]
    _ = A / (K + 1) * (lam⁻¹) ^ K * (lam⁻¹ * (lam / (lam - 1))) := by ring
    _ = A / (K + 1) * (lam⁻¹) ^ K * (lam - 1)⁻¹ := by rw [hcancel]
    _ = realInput40LogMTruncClosedBound A lam K := by
          simp [realInput40LogMTruncClosedBound, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

end

end Omega.SyncKernelWeighted
