import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

open Filter Topology

namespace Omega.POM

/-- The diagonal moment index `q_m = ⌊τ m⌋`. -/
noncomputable def pomDiagonalMomentIndex (τ : ℝ) (m : ℕ) : ℕ :=
  Nat.floor (τ * (m : ℝ))

/-- The quadratic-scale free energy along a diagonal family of moments. -/
noncomputable def pomDiagonalQuadraticFreeEnergy (S : ℕ → ℝ) (m : ℕ) : ℝ :=
  Real.log (S m) / (m : ℝ) ^ 2

private theorem tendsto_pomDiagonalMomentIndex_ratio (τ : ℝ) (hτ : 0 ≤ τ) :
    Tendsto (fun m : ℕ => (pomDiagonalMomentIndex τ m : ℝ) / (m : ℝ))
      atTop
      (nhds τ) := by
  have hinv : Tendsto (fun m : ℕ => (1 : ℝ) / (m : ℝ)) atTop (nhds 0) := by
    simpa [one_div, div_eq_mul_inv] using
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
  have hlower :
      Tendsto (fun m : ℕ => τ - (1 : ℝ) / (m : ℝ)) atTop (nhds τ) := by
    simpa [sub_eq_add_neg] using
      (tendsto_const_nhds.sub hinv)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds ?_ ?_
  · exact (eventually_ge_atTop 1).mono fun m hm => by
      have hm_pos : 0 < (m : ℝ) := by exact_mod_cast hm
      have hlt :
          τ * (m : ℝ) < (pomDiagonalMomentIndex τ m : ℝ) + 1 := by
        simpa [pomDiagonalMomentIndex] using
          (Nat.lt_floor_add_one (τ * (m : ℝ)))
      have hbound : τ - (1 : ℝ) / (m : ℝ) < (pomDiagonalMomentIndex τ m : ℝ) / (m : ℝ) := by
        have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
        field_simp [hm_ne]
        linarith
      exact le_of_lt hbound
  · exact (eventually_ge_atTop 1).mono fun m hm => by
      have hm_pos : 0 < (m : ℝ) := by exact_mod_cast hm
      have hfloor_le :
          (pomDiagonalMomentIndex τ m : ℝ) ≤ τ * (m : ℝ) := by
        refine Nat.floor_le ?_
        positivity
      have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
      field_simp [hm_ne]
      linarith

private theorem pom_diagonal_collapse_quadratic_free_energy_of_ratio
    (q : ℕ → ℕ) (Xcard M S : ℕ → ℝ) (τ αstar : ℝ)
    (hXcard_ge_one : ∀ m, 1 ≤ Xcard m)
    (hSandwich : ∀ m,
      Real.exp ((q m : ℝ) * Real.log (M m)) ≤ S m ∧
        S m ≤ Xcard m * Real.exp ((q m : ℝ) * Real.log (M m)))
    (hq :
      Tendsto (fun m : ℕ => (q m : ℝ) / (m : ℝ)) atTop (nhds τ))
    (hXcard :
      Tendsto (fun m : ℕ => Real.log (Xcard m) / (m : ℝ) ^ 2) atTop (nhds 0))
    (hM :
      Tendsto (fun m : ℕ => Real.log (M m) / (m : ℝ)) atTop (nhds αstar)) :
    Tendsto (pomDiagonalQuadraticFreeEnergy S) atTop (nhds (τ * αstar)) := by
  have hmain :
      Tendsto
        (fun m : ℕ => ((q m : ℝ) * Real.log (M m)) / (m : ℝ) ^ 2)
        atTop
        (nhds (τ * αstar)) := by
    have hprod :
        Tendsto
          (fun m : ℕ => ((q m : ℝ) / (m : ℝ)) * (Real.log (M m) / (m : ℝ)))
          atTop
          (nhds (τ * αstar)) := by
      simpa using hq.mul hM
    have heq :
        (fun m : ℕ => ((q m : ℝ) * Real.log (M m)) / (m : ℝ) ^ 2) =ᶠ[atTop]
          (fun m : ℕ => ((q m : ℝ) / (m : ℝ)) * (Real.log (M m) / (m : ℝ))) := by
      filter_upwards [eventually_ge_atTop 1] with m hm
      have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
      field_simp [hm_ne]
    exact hprod.congr' heq.symm
  have hupper :
      Tendsto
        (fun m : ℕ =>
          Real.log (Xcard m) / (m : ℝ) ^ 2 + ((q m : ℝ) * Real.log (M m)) / (m : ℝ) ^ 2)
        atTop
        (nhds (τ * αstar)) := by
    simpa [zero_add] using hXcard.add hmain
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hmain hupper ?_ ?_
  · exact (eventually_ge_atTop 1).mono fun m hm => by
      have hm_pos : 0 < (m : ℝ) := by exact_mod_cast hm
      have hm_sq_nonneg : 0 ≤ (m : ℝ) ^ 2 := sq_nonneg _
      have hlog_le :
          Real.log (Real.exp ((q m : ℝ) * Real.log (M m))) ≤ Real.log (S m) := by
        exact Real.log_le_log (Real.exp_pos _) (hSandwich m).1
      have hdiv :
          ((q m : ℝ) * Real.log (M m)) / (m : ℝ) ^ 2 ≤
            Real.log (S m) / (m : ℝ) ^ 2 := by
        simpa [Real.log_exp] using
          (div_le_div_of_nonneg_right hlog_le hm_sq_nonneg)
      simpa [pomDiagonalQuadraticFreeEnergy] using hdiv
  · exact (eventually_ge_atTop 1).mono fun m hm => by
      have hm_pos : 0 < (m : ℝ) := by exact_mod_cast hm
      have hm_sq_nonneg : 0 ≤ (m : ℝ) ^ 2 := sq_nonneg _
      have hXcard_pos : 0 < Xcard m := lt_of_lt_of_le zero_lt_one (hXcard_ge_one m)
      have hupper_log :
          Real.log (S m) ≤
            Real.log (Xcard m * Real.exp ((q m : ℝ) * Real.log (M m))) := by
        exact Real.log_le_log
          (lt_of_lt_of_le (Real.exp_pos _) (hSandwich m).1)
          (hSandwich m).2
      have hdiv :
          Real.log (S m) / (m : ℝ) ^ 2 ≤
            Real.log (Xcard m * Real.exp ((q m : ℝ) * Real.log (M m))) / (m : ℝ) ^ 2 := by
        exact div_le_div_of_nonneg_right hupper_log hm_sq_nonneg
      have hrewrite :
          Real.log (Xcard m * Real.exp ((q m : ℝ) * Real.log (M m))) / (m : ℝ) ^ 2 =
            Real.log (Xcard m) / (m : ℝ) ^ 2 + ((q m : ℝ) * Real.log (M m)) / (m : ℝ) ^ 2 := by
        rw [Real.log_mul (ne_of_gt hXcard_pos) (by positivity : Real.exp _ ≠ 0), Real.log_exp,
          add_div]
      calc
        pomDiagonalQuadraticFreeEnergy S m
            = Real.log (S m) / (m : ℝ) ^ 2 := by
                rfl
        _ ≤ Real.log (Xcard m * Real.exp ((q m : ℝ) * Real.log (M m))) / (m : ℝ) ^ 2 := hdiv
        _ = Real.log (Xcard m) / (m : ℝ) ^ 2 + ((q m : ℝ) * Real.log (M m)) / (m : ℝ) ^ 2 :=
          hrewrite

/-- Paper label: `thm:pom-diagonal-collapse-quadratic-free-energy`. -/
theorem paper_pom_diagonal_collapse_quadratic_free_energy
    (Xcard M S : ℕ → ℝ) (τ αstar : ℝ)
    (hτ : 0 ≤ τ)
    (hXcard_ge_one : ∀ m, 1 ≤ Xcard m)
    (hSandwich : ∀ m,
      Real.exp (((pomDiagonalMomentIndex τ m : ℝ)) * Real.log (M m)) ≤ S m ∧
        S m ≤
          Xcard m * Real.exp (((pomDiagonalMomentIndex τ m : ℝ)) * Real.log (M m)))
    (hXcard :
      Tendsto (fun m : ℕ => Real.log (Xcard m) / (m : ℝ) ^ 2) atTop (nhds 0))
    (hM :
      Tendsto (fun m : ℕ => Real.log (M m) / (m : ℝ)) atTop (nhds αstar)) :
    Tendsto (pomDiagonalQuadraticFreeEnergy S) atTop (nhds (τ * αstar)) := by
  refine pom_diagonal_collapse_quadratic_free_energy_of_ratio
    (q := pomDiagonalMomentIndex τ) Xcard M S τ αstar hXcard_ge_one hSandwich ?_ hXcard hM
  exact tendsto_pomDiagonalMomentIndex_ratio τ hτ

/-- Paper label: `cor:pom-diagonal-extract-alpha-star`. -/
theorem paper_pom_diagonal_extract_alpha_star (Xcard M S : ℕ → ℝ) (τ αstar : ℝ) (hτ : 0 < τ)
    (hdiag : Tendsto (pomDiagonalQuadraticFreeEnergy S) atTop (nhds (τ * αstar))) :
    Tendsto (fun m : ℕ => Real.log (S m) / (τ * (m : ℝ) ^ 2)) atTop (nhds αstar) := by
  have hτ_ne : τ ≠ 0 := ne_of_gt hτ
  simpa [pomDiagonalQuadraticFreeEnergy, div_eq_mul_inv, one_div, hτ_ne, mul_assoc, mul_left_comm,
    mul_comm] using hdiag.const_mul (1 / τ : ℝ)

end Omega.POM
