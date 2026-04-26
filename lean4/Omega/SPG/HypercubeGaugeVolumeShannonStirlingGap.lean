import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.SPG

open scoped BigOperators

noncomputable section

/-- The normalizing factor `2^n` as a real number. -/
def hypercube_gauge_volume_shannon_stirling_gap_pow2 (n : ℕ) : ℝ :=
  ((2 ^ n : ℕ) : ℝ)

/-- The pushforward mass of a fiber. -/
def hypercube_gauge_volume_shannon_stirling_gap_probability {X : Type*} [Fintype X]
    (n : ℕ) (d : X → ℕ) (x : X) : ℝ :=
  (d x : ℝ) / hypercube_gauge_volume_shannon_stirling_gap_pow2 n

/-- The gauge-volume density `g(f) = 2^{-n} ∑_x log(d_x!)`. -/
def hypercube_gauge_volume_shannon_stirling_gap_gauge_density {X : Type*} [Fintype X]
    (n : ℕ) (d : X → ℕ) : ℝ :=
  (1 / hypercube_gauge_volume_shannon_stirling_gap_pow2 n) *
    ∑ x, Real.log ((d x).factorial)

/-- The Shannon entropy of the pushforward distribution. -/
def hypercube_gauge_volume_shannon_stirling_gap_shannon {X : Type*} [Fintype X]
    (n : ℕ) (d : X → ℕ) : ℝ :=
  -∑ x, hypercube_gauge_volume_shannon_stirling_gap_probability n d x *
    Real.log (hypercube_gauge_volume_shannon_stirling_gap_probability n d x)

/-- The aggregated Stirling remainder. -/
def hypercube_gauge_volume_shannon_stirling_gap_remainder {X : Type*} [Fintype X]
    (n : ℕ) (r : X → ℝ) : ℝ :=
  (1 / hypercube_gauge_volume_shannon_stirling_gap_pow2 n) * ∑ x, r x

private lemma hypercube_gauge_volume_shannon_stirling_gap_pow2_pos (n : ℕ) :
    0 < hypercube_gauge_volume_shannon_stirling_gap_pow2 n := by
  unfold hypercube_gauge_volume_shannon_stirling_gap_pow2
  positivity

private lemma hypercube_gauge_volume_shannon_stirling_gap_log_pow2 (n : ℕ) :
    Real.log (hypercube_gauge_volume_shannon_stirling_gap_pow2 n) = (n : ℝ) * Real.log 2 := by
  unfold hypercube_gauge_volume_shannon_stirling_gap_pow2
  have h2pos : 0 < (2 : ℝ) := by norm_num
  calc
    Real.log (((2 ^ n : ℕ) : ℝ)) = Real.log ((2 : ℝ) ^ n) := by exact_mod_cast rfl
    _ = (n : ℝ) * Real.log 2 := by
      rw [← Real.rpow_natCast, Real.log_rpow h2pos]

/-- Paper label: `thm:hypercube-gauge-volume-shannon-stirling-gap`. Starting from the standalone
gauge-volume density `g(f)=2^{-n}\sum_x \log(d_x!)`, a fiberwise Stirling expansion with explicit
remainders rewrites the logarithmic main term as the Shannon deficit `n log 2 - H(p)` and bounds
the remaining error by the summed `1/(12 d_x)` correction. -/
theorem paper_hypercube_gauge_volume_shannon_stirling_gap
    {X : Type*} [Fintype X] (n : ℕ) (d : X → ℕ) (r : X → ℝ)
    (hd_pos : ∀ x, 0 < d x)
    (hsum : ∑ x, d x = 2 ^ n)
    (hstirling :
      ∀ x,
        Real.log ((d x).factorial) =
          (d x : ℝ) * Real.log (d x) - d x +
            (1 / 2 : ℝ) * Real.log (2 * Real.pi * d x) + r x)
    (hr_nonneg : ∀ x, 0 ≤ r x)
    (hr_le : ∀ x, r x ≤ 1 / (12 * d x)) :
    let g := hypercube_gauge_volume_shannon_stirling_gap_gauge_density n d
    let H := hypercube_gauge_volume_shannon_stirling_gap_shannon n d
    let R := hypercube_gauge_volume_shannon_stirling_gap_remainder n r
    g =
        (n : ℝ) * Real.log 2 - 1 - H +
          (1 / hypercube_gauge_volume_shannon_stirling_gap_pow2 n) *
            ∑ x, (1 / 2 : ℝ) * Real.log (2 * Real.pi * d x) + R ∧
      0 ≤ R ∧
      R ≤
        (1 / hypercube_gauge_volume_shannon_stirling_gap_pow2 n) *
          ∑ x, 1 / (12 * (d x : ℝ)) := by
  let N := hypercube_gauge_volume_shannon_stirling_gap_pow2 n
  let p := hypercube_gauge_volume_shannon_stirling_gap_probability n d
  let g := hypercube_gauge_volume_shannon_stirling_gap_gauge_density n d
  let H := hypercube_gauge_volume_shannon_stirling_gap_shannon n d
  let R := hypercube_gauge_volume_shannon_stirling_gap_remainder n r
  have hN_pos : 0 < N := hypercube_gauge_volume_shannon_stirling_gap_pow2_pos n
  have hN_ne : N ≠ 0 := ne_of_gt hN_pos
  have hsum_real : ∑ x, (d x : ℝ) = N := by
    unfold N hypercube_gauge_volume_shannon_stirling_gap_pow2
    exact_mod_cast hsum
  have hp_sum : ∑ x, p x = 1 := by
    calc
      ∑ x, p x = (∑ x, (d x : ℝ)) / N := by
        unfold p hypercube_gauge_volume_shannon_stirling_gap_probability
        rw [Finset.sum_div]
      _ = 1 := by
        rw [hsum_real]
        field_simp [hN_ne]
  have hp_log :
      ∑ x, p x * Real.log (p x) =
        (1 / N) * ∑ x, (d x : ℝ) * Real.log (d x) - Real.log N := by
    calc
      ∑ x, p x * Real.log (p x) =
          ∑ x, ((d x : ℝ) / N) * (Real.log (d x) - Real.log N) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            unfold p hypercube_gauge_volume_shannon_stirling_gap_probability
            have hd_ne : (d x : ℝ) ≠ 0 := by
              exact_mod_cast Nat.ne_of_gt (hd_pos x)
            rw [Real.log_div hd_ne hN_ne]
      _ =
          ∑ x, (((d x : ℝ) / N) * Real.log (d x) -
            ((d x : ℝ) / N) * Real.log N) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            ring
      _ =
          (∑ x, ((d x : ℝ) / N) * Real.log (d x)) -
            ∑ x, ((d x : ℝ) / N) * Real.log N := by
            rw [Finset.sum_sub_distrib]
      _ =
          (1 / N) * ∑ x, (d x : ℝ) * Real.log (d x) -
            (∑ x, (d x : ℝ) / N) * Real.log N := by
            congr 1
            · rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro x hx
              ring
            · rw [Finset.sum_mul]
      _ = (1 / N) * ∑ x, (d x : ℝ) * Real.log (d x) - Real.log N := by
            have hp_sum' : ∑ x, (d x : ℝ) / N = 1 := by
              simpa [p, hypercube_gauge_volume_shannon_stirling_gap_probability] using hp_sum
            rw [hp_sum']
            ring
  have hmain :
      (1 / N) * ∑ x, (d x : ℝ) * Real.log (d x) =
        (n : ℝ) * Real.log 2 - H := by
    have hH : ∑ x, p x * Real.log (p x) = -H := by
      simp [H, p, hypercube_gauge_volume_shannon_stirling_gap_shannon]
    rw [hypercube_gauge_volume_shannon_stirling_gap_log_pow2] at hp_log
    rw [hH] at hp_log
    linarith
  have hg :
      g =
        (1 / N) * ∑ x, (d x : ℝ) * Real.log (d x) - 1 +
          (1 / N) * ∑ x, (1 / 2 : ℝ) * Real.log (2 * Real.pi * d x) + R := by
    unfold g hypercube_gauge_volume_shannon_stirling_gap_gauge_density
      R hypercube_gauge_volume_shannon_stirling_gap_remainder
    calc
      (1 / N) * ∑ x, Real.log ((d x).factorial) =
          (1 / N) *
            ∑ x, ((d x : ℝ) * Real.log (d x) - d x +
              (1 / 2 : ℝ) * Real.log (2 * Real.pi * d x) + r x) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro x hx
            exact hstirling x
      _ =
          (1 / N) * ∑ x, ((d x : ℝ) * Real.log (d x)) -
            (1 / N) * ∑ x, (d x : ℝ) +
            (1 / N) * ∑ x, (1 / 2 : ℝ) * Real.log (2 * Real.pi * d x) +
            (1 / N) * ∑ x, r x := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib]
            ring
      _ =
          (1 / N) * ∑ x, ((d x : ℝ) * Real.log (d x)) - 1 +
            (1 / N) * ∑ x, (1 / 2 : ℝ) * Real.log (2 * Real.pi * d x) + R := by
            rw [show (1 / N) * ∑ x, r x = R by rfl]
            rw [hsum_real]
            field_simp [hN_ne]
  have hR_nonneg : 0 ≤ R := by
    unfold R hypercube_gauge_volume_shannon_stirling_gap_remainder
    exact mul_nonneg (one_div_nonneg.mpr hN_pos.le) (Finset.sum_nonneg fun x hx => hr_nonneg x)
  have hR_le :
      R ≤ (1 / N) * ∑ x, 1 / (12 * (d x : ℝ)) := by
    unfold R hypercube_gauge_volume_shannon_stirling_gap_remainder
    have hsum_le :
        ∑ x, r x ≤ ∑ x, 1 / (12 * (d x : ℝ)) := by
      exact Finset.sum_le_sum fun x hx => hr_le x
    exact mul_le_mul_of_nonneg_left hsum_le (one_div_nonneg.mpr hN_pos.le)
  have hg' :
      g =
        (n : ℝ) * Real.log 2 - 1 - H +
          (1 / N) * ∑ x, (1 / 2 : ℝ) * Real.log (2 * Real.pi * d x) + R := by
    calc
      g =
          (1 / N) * ∑ x, (d x : ℝ) * Real.log (d x) - 1 +
            (1 / N) * ∑ x, (1 / 2 : ℝ) * Real.log (2 * Real.pi * d x) + R := hg
      _ =
          (n : ℝ) * Real.log 2 - 1 - H +
            (1 / N) * ∑ x, (1 / 2 : ℝ) * Real.log (2 * Real.pi * d x) + R := by
            rw [hmain]
            ring
  refine ⟨by simpa [N, g, H, R] using hg', hR_nonneg, by simpa [N, R] using hR_le⟩

end

end Omega.SPG
