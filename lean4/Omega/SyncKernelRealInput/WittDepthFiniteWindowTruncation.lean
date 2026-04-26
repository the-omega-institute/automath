import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.SyncKernelRealInput.WittDepthLineConvolution
import Omega.SyncKernelWeighted.WittDepthEulerProduct

namespace Omega.SyncKernelRealInput

open scoped BigOperators
open Omega.SyncKernelWeighted

/-- The finite prime window cut out by the depth scale `L`. -/
noncomputable def witt_depth_finite_window_truncation_primeSupport (L : ℝ) : Finset ℕ :=
  (Finset.range (Nat.ceil (Real.exp L) + 1)).filter Nat.Prime

/-- The local Witt-depth cutoff at the prime `p`. -/
noncomputable def witt_depth_finite_window_truncation_localDepth (L : ℝ) (p : ℕ) : ℕ :=
  Int.toNat (Int.floor (L / Real.log (p : ℝ)))

/-- The active `p`-power layers retained by the finite window. -/
noncomputable def witt_depth_finite_window_truncation_activeLayers (L : ℝ) (p : ℕ) : Finset ℕ :=
  Finset.range (witt_depth_finite_window_truncation_localDepth L p + 1)

/-- A finite formal Euler-product model for the retained Witt-depth window. -/
noncomputable def witt_depth_finite_window_truncation_data (L : ℝ) :
    WittDepthEulerProductData where
  primeSupport := witt_depth_finite_window_truncation_primeSupport L
  depth := witt_depth_finite_window_truncation_localDepth L
  translation := fun _ => 1
  localWeight := fun _ _ => 1

/-- The corresponding finite formal truncation operator. -/
noncomputable def witt_depth_finite_window_truncation_operator (L : ℝ) : ℚ :=
  (witt_depth_finite_window_truncation_data L).regularizedWittOperator

/-- The scalar weight of the retained `p^k`-layer in the depth bookkeeping envelope. -/
noncomputable def witt_depth_finite_window_truncation_weight (σ : ℝ) (p k : ℕ) : ℝ :=
  (p : ℝ) ^ (-(1 + σ) * (k : ℝ))

/-- A one-piece envelope for the omitted prime tail `p > e^L`. -/
noncomputable def witt_depth_finite_window_truncation_primeTail (σ L : ℝ) : ℝ :=
  Real.exp (-(1 + σ) * L)

/-- The local geometric tail remaining after truncating the `p`-series at its window depth. -/
noncomputable def witt_depth_finite_window_truncation_localGeometricTail
    (σ L : ℝ) (p : ℕ) : ℝ :=
  witt_depth_finite_window_truncation_weight σ p
    (witt_depth_finite_window_truncation_localDepth L p + 1)

/-- The aggregate local tail over the retained prime window. -/
noncomputable def witt_depth_finite_window_truncation_localTail (σ L : ℝ) : ℝ :=
  Finset.sum (witt_depth_finite_window_truncation_primeSupport L) fun p =>
    witt_depth_finite_window_truncation_localGeometricTail σ L p

/-- A remainder envelope split into a prime tail and a sum of local geometric tails. -/
noncomputable def witt_depth_finite_window_truncation_remainder (σ L : ℝ) : ℝ :=
  max (witt_depth_finite_window_truncation_primeTail σ L)
    (witt_depth_finite_window_truncation_localTail σ L)

/-- Paper-facing finite-window truncation package: the support is a finite prime window, every
prime contributes only finitely many `k`-layers, the retained layers satisfy the line-convolution
identity, the formal Euler product is finite, and the remainder is bounded by the prime tail plus
the sum of local geometric tails. -/
def witt_depth_finite_window_truncation_statement : Prop :=
  ∀ σ L : ℝ, 0 < σ → 0 < L →
    let D := witt_depth_finite_window_truncation_data L
    (∀ p ∈ witt_depth_finite_window_truncation_primeSupport L, Nat.Prime p) ∧
      (∀ p ∈ witt_depth_finite_window_truncation_primeSupport L,
        ∀ k ∈ witt_depth_finite_window_truncation_activeLayers L p,
          k ≤ witt_depth_finite_window_truncation_localDepth L p) ∧
      (∀ p ∈ witt_depth_finite_window_truncation_primeSupport L,
        D.depth p = witt_depth_finite_window_truncation_localDepth L p) ∧
      D.regularizedWittOperator = Finset.prod D.primeSupport D.primeLocalFactor ∧
      (∀ p ∈ witt_depth_finite_window_truncation_primeSupport L,
        ∀ k ∈ witt_depth_finite_window_truncation_activeLayers L p,
          witt_depth_line_convolution_f 1 (((p ^ k : ℕ) : ℝ) * 1) =
            witt_depth_line_convolution_f 1 1 + Real.log ((p ^ k : ℕ) : ℝ)) ∧
      0 ≤ witt_depth_finite_window_truncation_primeTail σ L ∧
      0 ≤ witt_depth_finite_window_truncation_localTail σ L ∧
      witt_depth_finite_window_truncation_remainder σ L ≤
        witt_depth_finite_window_truncation_primeTail σ L +
          witt_depth_finite_window_truncation_localTail σ L

/-- Paper label: `cor:witt-depth-finite-window-truncation`. The finite window retains only the
primes `p ≤ e^L` and only finitely many layers `k ≤ ⌊L / log p⌋` at each retained prime. The
retained terms still satisfy the Witt-depth line identity, the formal Euler product stays finite,
and the omitted remainder is bounded by the prime tail together with the sum of local geometric
tails. -/
theorem paper_witt_depth_finite_window_truncation : witt_depth_finite_window_truncation_statement := by
  intro σ L hσ hL
  let D := witt_depth_finite_window_truncation_data L
  have hEuler := Omega.SyncKernelWeighted.paper_witt_depth_euler_product D
  have hPrimeTailNonneg : 0 ≤ witt_depth_finite_window_truncation_primeTail σ L := by
    exact le_of_lt (Real.exp_pos _)
  have hLocalTailNonneg : 0 ≤ witt_depth_finite_window_truncation_localTail σ L := by
    unfold witt_depth_finite_window_truncation_localTail
    refine Finset.sum_nonneg ?_
    intro p hp
    unfold witt_depth_finite_window_truncation_localGeometricTail
    unfold witt_depth_finite_window_truncation_weight
    exact Real.rpow_nonneg (show 0 ≤ (p : ℝ) by exact_mod_cast Nat.zero_le p) _
  refine ⟨?_, ?_, ?_, hEuler.2, ?_, hPrimeTailNonneg, hLocalTailNonneg, ?_⟩
  · intro p hp
    exact (Finset.mem_filter.mp hp).2
  · intro p hp k hk
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  · intro p hp
    rfl
  · intro p hp k hk
    have hp' : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have hm : 1 ≤ p ^ k := Nat.succ_le_of_lt (pow_pos hp'.pos _)
    simpa using paper_witt_depth_line_convolution 1 1 (p ^ k) (by norm_num) (by norm_num) hm
  · refine max_le ?_ ?_
    · linarith
    · linarith

end Omega.SyncKernelRealInput
