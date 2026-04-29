import Omega.POM.GreenKernelEntries

namespace Omega.POM

lemma pom_lk_exponential_clustering_gaplaw_sinh_le_half_exp (x : ℝ) :
    Real.sinh x ≤ Real.exp x / 2 := by
  rw [Real.sinh_eq]
  have hneg : 0 ≤ Real.exp (-x) := (Real.exp_pos (-x)).le
  nlinarith

lemma pom_lk_exponential_clustering_gaplaw_cosh_le_exp {x : ℝ} (hx : 0 ≤ x) :
    Real.cosh x ≤ Real.exp x := by
  rw [Real.cosh_eq]
  have hexp : Real.exp (-x) ≤ Real.exp x := Real.exp_le_exp.mpr (by linarith)
  nlinarith

lemma pom_lk_exponential_clustering_gaplaw_half_exp_le_cosh (x : ℝ) :
    Real.exp x / 2 ≤ Real.cosh x := by
  rw [Real.cosh_eq]
  have hneg : 0 ≤ Real.exp (-x) := (Real.exp_pos (-x)).le
  nlinarith

lemma pom_lk_exponential_clustering_gaplaw_div_mul_eq (x s c : ℝ) (hs : s ≠ 0)
    (hc : c ≠ 0) :
    x / (s * c) = (1 / s) * (x / c) := by
  field_simp [hs, hc]

/-- Paper label: `cor:pom-Lk-exponential-clustering-gaplaw`. -/
theorem paper_pom_lk_exponential_clustering_gaplaw (k i j : ℕ) (t : ℝ)
    (hη : 0 < pomEta t) (hij : 1 ≤ i ∧ i ≤ j ∧ j ≤ k) :
    pomLkGreenEntry k t i j ≤
      (1 / Real.sinh (2 * pomEta t)) *
        Real.exp (-2 * pomEta t * (((j - i : ℕ) : ℝ))) := by
  set η := pomEta t
  set a : ℝ := (2 * i : ℝ) * η
  set b : ℝ := (2 * (k - j) + 1 : ℝ) * η
  set c : ℝ := (2 * k + 1 : ℝ) * η
  have hη' : 0 < η := by simpa [η] using hη
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    positivity
  have hb_nonneg : 0 ≤ b := by
    dsimp [b]
    have hkj_real : (j : ℝ) ≤ k := by exact_mod_cast hij.2.2
    have hcoef : 0 ≤ 2 * ((k : ℝ) - j) + 1 := by nlinarith
    exact mul_nonneg hcoef hη'.le
  have hsinh_a : Real.sinh a ≤ Real.exp a / 2 :=
    pom_lk_exponential_clustering_gaplaw_sinh_le_half_exp a
  have hcosh_b : Real.cosh b ≤ Real.exp b :=
    pom_lk_exponential_clustering_gaplaw_cosh_le_exp hb_nonneg
  have hcosh_c : Real.exp c / 2 ≤ Real.cosh c :=
    pom_lk_exponential_clustering_gaplaw_half_exp_le_cosh c
  have hnum_nonneg : 0 ≤ Real.sinh a * Real.cosh b := by
    exact mul_nonneg (Real.sinh_nonneg_iff.mpr ha_nonneg) (Real.cosh_pos b).le
  have hnum_le : Real.sinh a * Real.cosh b ≤ (Real.exp a / 2) * Real.exp b := by
    exact mul_le_mul hsinh_a hcosh_b (Real.cosh_pos b).le (by positivity)
  have hden_pos : 0 < Real.exp c / 2 := by positivity
  have hratio :
      (Real.sinh a * Real.cosh b) / Real.cosh c ≤
        Real.exp (-2 * η * (((j - i : ℕ) : ℝ))) := by
    calc
      (Real.sinh a * Real.cosh b) / Real.cosh c
          ≤ ((Real.exp a / 2) * Real.exp b) / (Real.exp c / 2) := by
            exact div_le_div₀ (by positivity) hnum_le hden_pos hcosh_c
      _ = Real.exp (a + b - c) := by
            rw [Real.exp_sub, Real.exp_add]
            field_simp [Real.exp_ne_zero]
      _ = Real.exp (-2 * η * (((j - i : ℕ) : ℝ))) := by
            congr 1
            have hkj : ((k - j : ℕ) : ℝ) = (k : ℝ) - j := by
              exact Nat.cast_sub hij.2.2
            have hji : ((j - i : ℕ) : ℝ) = (j : ℝ) - i := by
              exact Nat.cast_sub hij.2.1
            simp [a, b, c, hji]
            ring
  have hsinh_pos : 0 < Real.sinh (2 * η) := by
    have htwo : 0 < (2 : ℝ) * η := by positivity
    exact Real.sinh_pos_iff.mpr htwo
  calc
    pomLkGreenEntry k t i j
        = (1 / Real.sinh (2 * η)) * ((Real.sinh a * Real.cosh b) / Real.cosh c) := by
          rw [pomLkGreenEntry]
          simpa [a, b, c, η] using
            pom_lk_exponential_clustering_gaplaw_div_mul_eq
              (Real.sinh a * Real.cosh b) (Real.sinh (2 * η)) (Real.cosh c)
              hsinh_pos.ne' (Real.cosh_pos c).ne'
    _ ≤ (1 / Real.sinh (2 * η)) *
          Real.exp (-2 * η * (((j - i : ℕ) : ℝ))) := by
          have hleft_nonneg : 0 ≤ 1 / Real.sinh (2 * η) :=
            one_div_nonneg.mpr hsinh_pos.le
          exact mul_le_mul_of_nonneg_left hratio hleft_nonneg
    _ = (1 / Real.sinh (2 * pomEta t)) *
          Real.exp (-2 * pomEta t * (((j - i : ℕ) : ℝ))) := by
          simp [η]

end Omega.POM
