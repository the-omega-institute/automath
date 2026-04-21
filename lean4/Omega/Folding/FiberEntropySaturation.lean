import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Folding.Fiber

namespace Omega

open scoped BigOperators

/-- Jensen saturation for the finite fiber-multiplicity observable:
`E_π[log d_m(X)] ≤ log E_π[d_m(X)]`, with equality exactly when the positive-`π` support sees a
single fiber multiplicity. For the uniform visible baseline, the expected multiplicity is the
average fiber size `|Ω_m| / |X_m| = 2^m / |X_m|`.
    cor:fold-fiber-entropy-saturation -/
theorem paper_fold_fiber_entropy_saturation (m : ℕ) (π : X m → ℝ)
    (hπ_nonneg : ∀ x, 0 ≤ π x) (hπ_sum : Finset.univ.sum π = 1) :
    (∑ x : X m, π x * Real.log (X.fiberMultiplicity x) ≤
      Real.log (∑ x : X m, π x * (X.fiberMultiplicity x : ℝ))) ∧
      ((∑ x : X m, π x * Real.log (X.fiberMultiplicity x) =
          Real.log (∑ x : X m, π x * (X.fiberMultiplicity x : ℝ))) ↔
        ∀ x : X m, π x ≠ 0 →
          (X.fiberMultiplicity x : ℝ) = ∑ y : X m, π y * (X.fiberMultiplicity y : ℝ)) ∧
      (∑ x : X m, ((1 : ℝ) / Fintype.card (X m)) * (X.fiberMultiplicity x : ℝ) =
        ((2 : ℝ) ^ m) / Fintype.card (X m)) ∧
      (∑ x : X m, ((1 : ℝ) / Fintype.card (X m)) * Real.log (X.fiberMultiplicity x) ≤
        Real.log (((2 : ℝ) ^ m) / Fintype.card (X m))) := by
  have hConcave : ConcaveOn ℝ (Set.Ioi (0 : ℝ)) Real.log := strictConcaveOn_log_Ioi.concaveOn
  have hStrictConcave : StrictConcaveOn ℝ (Set.Ioi (0 : ℝ)) Real.log :=
    strictConcaveOn_log_Ioi
  have hmem :
      ∀ x ∈ (Finset.univ : Finset (X m)), ((X.fiberMultiplicity x : ℕ) : ℝ) ∈ Set.Ioi (0 : ℝ) := by
    intro x hx
    show (0 : ℝ) < (X.fiberMultiplicity x : ℝ)
    exact_mod_cast X.fiberMultiplicity_pos x
  have hJensen :
      ∑ x : X m, π x * Real.log (X.fiberMultiplicity x) ≤
        Real.log (∑ x : X m, π x * (X.fiberMultiplicity x : ℝ)) := by
    simpa [smul_eq_mul] using
      (ConcaveOn.le_map_sum
        (t := (Finset.univ : Finset (X m))) (w := π)
        (p := fun x : X m => (X.fiberMultiplicity x : ℝ))
        hConcave (by intro x hx; exact hπ_nonneg x) hπ_sum hmem)
  have hEqIff₀ :
      Real.log (∑ x : X m, π x * (X.fiberMultiplicity x : ℝ)) =
        ∑ x : X m, π x * Real.log (X.fiberMultiplicity x) ↔
        ∀ x : X m, π x ≠ 0 →
          (X.fiberMultiplicity x : ℝ) = ∑ y : X m, π y * (X.fiberMultiplicity y : ℝ) := by
    simpa [smul_eq_mul] using
      (StrictConcaveOn.map_sum_eq_iff'
        (t := (Finset.univ : Finset (X m))) (w := π)
        (p := fun x : X m => (X.fiberMultiplicity x : ℝ))
        hStrictConcave (by intro x hx; exact hπ_nonneg x) hπ_sum hmem)
  have hEqIff :
      (∑ x : X m, π x * Real.log (X.fiberMultiplicity x) =
          Real.log (∑ x : X m, π x * (X.fiberMultiplicity x : ℝ))) ↔
        ∀ x : X m, π x ≠ 0 →
          (X.fiberMultiplicity x : ℝ) = ∑ y : X m, π y * (X.fiberMultiplicity y : ℝ) := by
    constructor
    · intro h
      exact hEqIff₀.mp h.symm
    · intro h
      exact (hEqIff₀.mpr h).symm
  have hcard_pos : 0 < (Fintype.card (X m) : ℝ) := by
    rw [X.card_eq_fib]
    exact_mod_cast fib_succ_pos (m + 1)
  have hUnif_nonneg : ∀ x : X m, 0 ≤ (1 : ℝ) / Fintype.card (X m) := by
    intro x
    positivity
  have hUnif_sum : ∑ x : X m, (1 : ℝ) / Fintype.card (X m) = 1 := by
    simp [hcard_pos.ne']
  have hUnifJensen :
      ∑ x : X m, ((1 : ℝ) / Fintype.card (X m)) * Real.log (X.fiberMultiplicity x) ≤
        Real.log (∑ x : X m, ((1 : ℝ) / Fintype.card (X m)) * (X.fiberMultiplicity x : ℝ)) := by
    simpa [smul_eq_mul] using
      (ConcaveOn.le_map_sum
        (t := (Finset.univ : Finset (X m)))
        (w := fun _ : X m => (1 : ℝ) / Fintype.card (X m))
        (p := fun x : X m => (X.fiberMultiplicity x : ℝ))
        hConcave (by intro x hx; exact hUnif_nonneg x) hUnif_sum hmem)
  have hUnifMean :
      ∑ x : X m, ((1 : ℝ) / Fintype.card (X m)) * (X.fiberMultiplicity x : ℝ) =
        ((2 : ℝ) ^ m) / Fintype.card (X m) := by
    calc
      ∑ x : X m, ((1 : ℝ) / Fintype.card (X m)) * (X.fiberMultiplicity x : ℝ) =
          ((1 : ℝ) / Fintype.card (X m)) * ∑ x : X m, (X.fiberMultiplicity x : ℝ) := by
            rw [Finset.mul_sum]
      _ = ((1 : ℝ) / Fintype.card (X m)) * ((2 ^ m : ℕ) : ℝ) := by
            congr 1
            exact_mod_cast X.fiberMultiplicity_sum_eq_pow m
      _ = ((1 : ℝ) / Fintype.card (X m)) * ((2 : ℝ) ^ m) := by
            congr 1
            exact_mod_cast (show 2 ^ m = 2 ^ m by rfl)
      _ = ((2 : ℝ) ^ m) / Fintype.card (X m) := by
            rw [div_eq_mul_inv]
            ring
  rw [hUnifMean] at hUnifJensen
  exact ⟨hJensen, hEqIff, hUnifMean, hUnifJensen⟩

end Omega

namespace Omega.Folding

/-- Paper label: `cor:fold-fiber-entropy-saturation`. -/
theorem paper_fold_fiber_entropy_saturation {X : Type*} [Fintype X] (pi : X → ℝ) (d : X → ℕ)
    (hpi_nonneg : ∀ x, 0 ≤ pi x) (hpi_sum : ∑ x, pi x = 1) (hd : ∀ x, 0 < d x) :
    (∑ x, pi x * Real.log (d x : ℝ)) ≤ Real.log (∑ x, pi x * d x) ∧
      ((∑ x, pi x * Real.log (d x : ℝ)) = Real.log (∑ x, pi x * d x) ↔
        ∃ c : ℕ, ∀ x, pi x ≠ 0 → d x = c) := by
  classical
  let M : ℝ := ∑ x, pi x * d x
  have hsupport : ∃ x, pi x ≠ 0 := by
    by_contra hnone
    have hzero : ∀ x, pi x = 0 := by
      simpa using hnone
    have hsum_zero : (∑ x, pi x) = 0 := by
      simp [hzero]
    linarith
  have hd_ge_one : ∀ x, (1 : ℝ) ≤ d x := by
    intro x
    exact_mod_cast Nat.succ_le_of_lt (hd x)
  have hM_ge_one : (1 : ℝ) ≤ M := by
    calc
      (1 : ℝ) = ∑ x, pi x * (1 : ℝ) := by simp [hpi_sum]
      _ ≤ ∑ x, pi x * d x := by
        refine Finset.sum_le_sum ?_
        intro x hx
        exact mul_le_mul_of_nonneg_left (hd_ge_one x) (hpi_nonneg x)
      _ = M := by rfl
  have hM_pos : 0 < M := by
    linarith
  have hsum_log_div :
      (∑ x, pi x * Real.log ((d x : ℝ) / M)) = (∑ x, pi x * Real.log (d x : ℝ)) - Real.log M := by
    calc
      (∑ x, pi x * Real.log ((d x : ℝ) / M))
          = ∑ x, pi x * (Real.log (d x : ℝ) - Real.log M) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              rw [Real.log_div (show (d x : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt (hd x))) hM_pos.ne']
      _ = ∑ x, (pi x * Real.log (d x : ℝ) - pi x * Real.log M) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            ring
      _ = (∑ x, pi x * Real.log (d x : ℝ)) - ∑ x, pi x * Real.log M := by
            rw [Finset.sum_sub_distrib]
      _ = (∑ x, pi x * Real.log (d x : ℝ)) - (∑ x, pi x) * Real.log M := by
            congr 1
            calc
              (∑ x, pi x * Real.log M) = ∑ x, Real.log M * pi x := by
                  refine Finset.sum_congr rfl ?_
                  intro x hx
                  ring
              _ = Real.log M * ∑ x, pi x := by
                  rw [Finset.mul_sum]
              _ = (∑ x, pi x) * Real.log M := by
                  ring
      _ = (∑ x, pi x * Real.log (d x : ℝ)) - Real.log M := by
            rw [hpi_sum, one_mul]
  have hsum_affine :
      (∑ x, pi x * (((d x : ℝ) / M) - 1)) = 0 := by
    calc
      (∑ x, pi x * (((d x : ℝ) / M) - 1))
          = ∑ x, ((pi x * d x) / M - pi x) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              ring
      _ = (∑ x, (pi x * d x) / M) - ∑ x, pi x := by
            rw [Finset.sum_sub_distrib]
      _ = (∑ x, pi x * d x) / M - ∑ x, pi x := by
            rw [Finset.sum_div]
      _ = M / M - 1 := by
            simp [M, hpi_sum]
      _ = 1 - 1 := by
            field_simp [hM_pos.ne']
      _ = 0 := by
            ring
  have hineq : (∑ x, pi x * Real.log (d x : ℝ)) ≤ Real.log M := by
    have hpointwise :
        ∀ x, pi x * Real.log ((d x : ℝ) / M) ≤ pi x * (((d x : ℝ) / M) - 1) := by
      intro x
      have hz_pos : 0 < (d x : ℝ) / M := by
        exact div_pos (by exact_mod_cast hd x) hM_pos
      exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hz_pos) (hpi_nonneg x)
    have hsum_le :
        (∑ x, pi x * Real.log ((d x : ℝ) / M)) ≤ ∑ x, pi x * (((d x : ℝ) / M) - 1) := by
      exact Finset.sum_le_sum (s := Finset.univ) (fun x hx => hpointwise x)
    rw [hsum_log_div, hsum_affine] at hsum_le
    linarith
  refine ⟨by simpa [M] using hineq, ?_⟩
  constructor
  · intro hEq
    have hEqM : (∑ x, pi x * Real.log (d x : ℝ)) = Real.log M := by
      simpa [M] using hEq
    let δ : X → ℝ := fun x => pi x * ((((d x : ℝ) / M) - 1) - Real.log ((d x : ℝ) / M))
    have hδ_nonneg : ∀ x, 0 ≤ δ x := by
      intro x
      have hz_pos : 0 < (d x : ℝ) / M := by
        exact div_pos (by exact_mod_cast hd x) hM_pos
      have hinner_nonneg : 0 ≤ (((d x : ℝ) / M) - 1) - Real.log ((d x : ℝ) / M) := by
        linarith [Real.log_le_sub_one_of_pos hz_pos]
      exact mul_nonneg (hpi_nonneg x) hinner_nonneg
    have hδ_sum : (∑ x, δ x) = 0 := by
      calc
        (∑ x, δ x)
            = ∑ x, (pi x * (((d x : ℝ) / M) - 1) - pi x * Real.log ((d x : ℝ) / M)) := by
                  refine Finset.sum_congr rfl ?_
                  intro x hx
                  unfold δ
                  ring
        _ = (∑ x, pi x * (((d x : ℝ) / M) - 1)) -
              (∑ x, pi x * Real.log ((d x : ℝ) / M)) := by
                rw [Finset.sum_sub_distrib]
        _ = 0 - ((∑ x, pi x * Real.log (d x : ℝ)) - Real.log M) := by
              rw [hsum_affine, hsum_log_div]
        _ = 0 := by
              linarith [hEqM]
    have hδ_zero := (Fintype.sum_eq_zero_iff_of_nonneg (f := δ) hδ_nonneg).1 hδ_sum
    obtain ⟨x0, hx0⟩ := hsupport
    have hconst_real : ∀ x, pi x ≠ 0 → (d x : ℝ) = M := by
      intro x hx
      have hδx : δ x = 0 := by
        simpa using congrFun hδ_zero x
      have hpi_pos : 0 < pi x := by
        exact lt_of_le_of_ne (hpi_nonneg x) (Ne.symm hx)
      have hz_pos : 0 < (d x : ℝ) / M := by
        exact div_pos (by exact_mod_cast hd x) hM_pos
      have hinner_zero : (((d x : ℝ) / M) - 1) - Real.log ((d x : ℝ) / M) = 0 := by
        nlinarith
      have hratio_eq_one : (d x : ℝ) / M = 1 := by
        by_contra hne
        have hstrict : Real.log ((d x : ℝ) / M) < ((d x : ℝ) / M) - 1 := by
          exact Real.log_lt_sub_one_of_pos hz_pos hne
        linarith
      simpa using (div_eq_iff hM_pos.ne').1 hratio_eq_one
    refine ⟨d x0, ?_⟩
    intro x hx
    have hx_real : (d x : ℝ) = M := hconst_real x hx
    have hx0_real : (d x0 : ℝ) = M := hconst_real x0 hx0
    have : (d x : ℝ) = (d x0 : ℝ) := by
      linarith
    exact Nat.cast_inj.mp this
  · rintro ⟨c, hc⟩
    obtain ⟨x0, hx0⟩ := hsupport
    have hsum_log_eq : (∑ x, pi x * Real.log (d x : ℝ)) = Real.log (c : ℝ) := by
      calc
        (∑ x, pi x * Real.log (d x : ℝ)) = ∑ x, pi x * Real.log (c : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            by_cases hpi0 : pi x = 0
            · simp [hpi0]
            · rw [hc x hpi0]
        _ = ∑ x, Real.log (c : ℝ) * pi x := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            ring
        _ = Real.log (c : ℝ) * ∑ x, pi x := by
            rw [Finset.mul_sum]
        _ = Real.log (c : ℝ) := by
            rw [hpi_sum, mul_one]
    have hM_eq : M = c := by
      calc
        M = ∑ x, pi x * (c : ℝ) := by
              unfold M
              refine Finset.sum_congr rfl ?_
              intro x hx
              by_cases hpi0 : pi x = 0
              · simp [hpi0]
              · rw [hc x hpi0]
        _ = ∑ x, (c : ℝ) * pi x := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              ring
        _ = c * ∑ x, pi x := by
              rw [Finset.mul_sum]
        _ = c := by
              rw [hpi_sum, mul_one]
    calc
      (∑ x, pi x * Real.log (d x : ℝ)) = Real.log (c : ℝ) := hsum_log_eq
      _ = Real.log M := by rw [hM_eq]

end Omega.Folding
