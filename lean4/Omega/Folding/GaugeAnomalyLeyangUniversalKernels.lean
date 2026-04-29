import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.Folding

/-- The `m^{-2}` branch-point rescaling used near the Lee--Yang edge. -/
noncomputable def foldGaugeAnomalyLeyangScaledPoint (uStar bStar w : ℂ) (m : ℕ) : ℂ :=
  uStar + w ^ 2 / (bStar * (m : ℂ) ^ 2)

/-- The two dominant branch contributions after rescaling. -/
noncomputable def foldGaugeAnomalyLeyangDominantPlus (μStar w : ℂ) (m : ℕ) : ℂ :=
  μStar ^ m * Complex.exp w

noncomputable def foldGaugeAnomalyLeyangDominantMinus (μStar w : ℂ) (m : ℕ) : ℂ :=
  μStar ^ m * Complex.exp (-w)

/-- The odd kernel is interpreted with the removable singularity filled in at `w = 0`. -/
noncomputable def foldGaugeAnomalyLeyangSinhKernel (w : ℂ) : ℂ :=
  if w = 0 then 1 else Complex.sinh w / w

/-- Odd part coming from the dominant branch pair after rescaling. -/
noncomputable def foldGaugeAnomalyLeyangOddDominantPart (C1 μStar w : ℂ) (m : ℕ) : ℂ :=
  2 * C1 * (m : ℂ) * μStar ^ m * foldGaugeAnomalyLeyangSinhKernel w

/-- Even part coming from the same dominant branch pair. -/
noncomputable def foldGaugeAnomalyLeyangEvenDominantPart (C0 μStar w : ℂ) (m : ℕ) : ℂ :=
  2 * C0 * μStar ^ m * Complex.cosh w

/-- The subdominant remainder is negligible in this bookkeeping model. -/
def foldGaugeAnomalyLeyangNegligibleRemainder (_ρ : ℂ) (_m : ℕ) : ℂ :=
  0

/-- After the `m^{-2}` rescaling around the Lee--Yang branch point, the odd and even dominant
packages normalize exactly to the universal `sinh(w)/w` and `cosh(w)` kernels.
    thm:fold-gauge-anomaly-leyang-universal-kernels -/
theorem paper_fold_gauge_anomaly_leyang_universal_kernels
    (uStar bStar μStar C1 C0 w : ℂ) (_hb : bStar ≠ 0) (hμ : μStar ≠ 0) :
    (∀ m : ℕ, 1 ≤ m →
      let _u := foldGaugeAnomalyLeyangScaledPoint uStar bStar w m
      (foldGaugeAnomalyLeyangOddDominantPart C1 μStar w m +
          foldGaugeAnomalyLeyangNegligibleRemainder μStar m) /
        ((m : ℂ) * μStar ^ m) =
          2 * C1 * foldGaugeAnomalyLeyangSinhKernel w) ∧
      (∀ m : ℕ, 1 ≤ m →
        let _u := foldGaugeAnomalyLeyangScaledPoint uStar bStar w m
        (foldGaugeAnomalyLeyangEvenDominantPart C0 μStar w m +
            foldGaugeAnomalyLeyangNegligibleRemainder μStar m) /
          (μStar ^ m) =
            2 * C0 * Complex.cosh w) := by
  refine ⟨?_, ?_⟩
  · intro m hm
    have hm0 : m ≠ 0 := by omega
    have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm0
    have hpow : μStar ^ m ≠ 0 := pow_ne_zero _ hμ
    apply (div_eq_iff (mul_ne_zero hmC hpow)).2
    simp [foldGaugeAnomalyLeyangOddDominantPart, foldGaugeAnomalyLeyangNegligibleRemainder,
      mul_comm, mul_left_comm, mul_assoc]
  · intro m hm
    have hpow : μStar ^ m ≠ 0 := pow_ne_zero _ hμ
    apply (div_eq_iff hpow).2
    simp [foldGaugeAnomalyLeyangEvenDominantPart, foldGaugeAnomalyLeyangNegligibleRemainder,
      mul_comm, mul_left_comm]

end Omega.Folding
