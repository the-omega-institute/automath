import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-D-spectral-decomposition-fourperiod`. -/
theorem paper_pom_d_spectral_decomposition_fourperiod
    (D : ℕ → ℝ) (h0 : D 0 = 1) (h1 : D 1 = 2)
    (hrec : ∀ m : ℕ, D (m + 4) = D (m + 2) + D m) :
    ∃ a b c d : ℝ, ∀ m : ℕ,
      D m =
        a * (Real.sqrt Real.goldenRatio) ^ m +
          b * (-Real.sqrt Real.goldenRatio) ^ m +
            (Real.sqrt Real.goldenRatio)⁻¹ ^ m *
              (c * Real.cos (Real.pi * (m : ℝ) / 2) +
                d * Real.sin (Real.pi * (m : ℝ) / 2)) := by
  classical
  let φ : ℝ := Real.goldenRatio
  let r : ℝ := Real.sqrt φ
  let q : ℝ := r⁻¹
  let μ : ℝ := φ + φ⁻¹
  let s : ℝ := (D 2 + φ⁻¹) / μ
  let t : ℝ := (D 3 + 2 * φ⁻¹) / (r * μ)
  let a : ℝ := (s + t) / 2
  let b : ℝ := (s - t) / 2
  let c : ℝ := 1 - s
  let d : ℝ := r * (2 - r * t)
  refine ⟨a, b, c, d, ?_⟩
  let θ : ℕ → ℝ := fun m => Real.pi * (m : ℝ) / 2
  let X : ℕ → ℝ := fun m => c * Real.cos (θ m) + d * Real.sin (θ m)
  let G : ℕ → ℝ := fun m => a * r ^ m + b * (-r) ^ m + q ^ m * X m
  have hφ_pos : 0 < φ := by simpa [φ] using Real.goldenRatio_pos
  have hφ_ne : φ ≠ 0 := ne_of_gt hφ_pos
  have hr_nonneg : 0 ≤ r := by exact Real.sqrt_nonneg φ
  have hr_pos : 0 < r := by
    dsimp [r]
    exact Real.sqrt_pos_of_pos hφ_pos
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have hr_sq : r ^ 2 = φ := by
    dsimp [r]
    exact Real.sq_sqrt hφ_pos.le
  have hr_four : r ^ 4 = r ^ 2 + 1 := by
    calc
      r ^ 4 = φ ^ 2 := by rw [show r ^ 4 = (r ^ 2) ^ 2 by ring, hr_sq]
      _ = φ + 1 := by simp [φ, Real.goldenRatio_sq]
      _ = r ^ 2 + 1 := by rw [hr_sq]
  have hneg_r_four : (-r) ^ 4 = (-r) ^ 2 + 1 := by
    rw [show (-r) ^ 4 = r ^ 4 by ring, show (-r) ^ 2 = r ^ 2 by ring, hr_four]
  have hq_sq : q ^ 2 = φ⁻¹ := by
    dsimp [q]
    rw [inv_pow, hr_sq]
  have hq_four : q ^ 4 = 1 - q ^ 2 := by
    have hφ_sq : φ ^ 2 = φ + 1 := by simp [φ, Real.goldenRatio_sq]
    have hmain : φ⁻¹ ^ 2 = 1 - φ⁻¹ := by
      field_simp [hφ_ne]
      nlinarith [hφ_sq]
    calc
      q ^ 4 = (q ^ 2) ^ 2 := by ring
      _ = φ⁻¹ ^ 2 := by rw [hq_sq]
      _ = 1 - φ⁻¹ := hmain
      _ = 1 - q ^ 2 := by rw [hq_sq]
  have hμ_pos : 0 < μ := by
    have hφ_inv_pos : 0 < φ⁻¹ := inv_pos.mpr hφ_pos
    dsimp [μ]
    positivity
  have hμ_ne : μ ≠ 0 := ne_of_gt hμ_pos
  have hrμ_ne : r * μ ≠ 0 := mul_ne_zero hr_ne hμ_ne
  have hX_two : ∀ m : ℕ, X (m + 2) = -X m := by
    intro m
    have hθ : θ (m + 2) = θ m + Real.pi := by
      dsimp [θ]
      norm_num
      ring
    simp [X, hθ, Real.cos_add_pi, Real.sin_add_pi]
    ring
  have hX_four : ∀ m : ℕ, X (m + 4) = X m := by
    intro m
    have hθ : θ (m + 4) = θ m + 2 * Real.pi := by
      dsimp [θ]
      norm_num
      ring
    simp [X, hθ, Real.cos_add_two_pi, Real.sin_add_two_pi]
  have hGrec : ∀ m : ℕ, G (m + 4) = G (m + 2) + G m := by
    intro m
    dsimp [G]
    rw [hX_four m, hX_two m]
    simp only [pow_add]
    rw [hr_four, hneg_r_four, hq_four]
    ring
  have hG0 : G 0 = D 0 := by
    dsimp [G, X, θ, a, b, c]
    rw [h0]
    norm_num
    ring
  have hG1 : G 1 = D 1 := by
    have hqt : q * d = 2 - r * t := by
      dsimp [q, d]
      field_simp [hr_ne]
    dsimp [G, X, θ, a, b]
    norm_num
    rw [h1]
    rw [hqt]
    ring
  have hG2 : G 2 = D 2 := by
    have hs_eq : μ * s = D 2 + φ⁻¹ := by
      dsimp [s]
      field_simp [hμ_ne]
    dsimp [μ] at hs_eq
    dsimp [G, X, θ, a, b, c]
    norm_num
    rw [hr_sq, hq_sq]
    nlinarith [hs_eq]
  have hG3 : G 3 = D 3 := by
    have ht_eq : r * μ * t = D 3 + 2 * φ⁻¹ := by
      dsimp [t]
      field_simp [hrμ_ne]
    have hsin_three : Real.sin (Real.pi * (3 : ℝ) / 2) = -1 := by
      have hθ : Real.pi * (3 : ℝ) / 2 = Real.pi / 2 + Real.pi := by ring
      rw [hθ, Real.sin_add_pi, Real.sin_pi_div_two]
    have hcos_three : Real.cos (Real.pi * (3 : ℝ) / 2) = 0 := by
      have hθ : Real.pi * (3 : ℝ) / 2 = Real.pi / 2 + Real.pi := by ring
      rw [hθ, Real.cos_add_pi, Real.cos_pi_div_two]
      norm_num
    have hq3d : q ^ 3 * d = φ⁻¹ * (2 - r * t) := by
      dsimp [q, d]
      field_simp [hr_ne]
      rw [show r ^ 2 = φ by exact hr_sq]
      ring
    dsimp [G, X, θ, a, b]
    rw [hcos_three, hsin_three]
    norm_num
    rw [hq3d]
    rw [show (s + t) / 2 * r ^ 3 + (s - t) / 2 * (-r) ^ 3 +
        -(φ⁻¹ * (2 - r * t)) = t * r ^ 3 - φ⁻¹ * (2 - r * t) by ring]
    rw [show r ^ 3 = r * φ by rw [show r ^ 3 = r * r ^ 2 by ring, hr_sq]]
    dsimp [μ] at ht_eq
    nlinarith [ht_eq]
  have hDG : ∀ k : ℕ, D k = G k := by
    intro k
    have hblock :
        ∀ n : ℕ,
          D n = G n ∧ D (n + 1) = G (n + 1) ∧
            D (n + 2) = G (n + 2) ∧ D (n + 3) = G (n + 3) := by
      intro n
      induction n with
      | zero =>
          exact ⟨by simpa using hG0.symm, by simpa using hG1.symm, by simpa using hG2.symm,
            by simpa using hG3.symm⟩
      | succ n ih =>
          refine ⟨ih.2.1, ih.2.2.1, ih.2.2.2, ?_⟩
          calc
            D (n + 1 + 3) = D (n + 4) := by ring_nf
            _ = D (n + 2) + D n := hrec n
            _ = G (n + 2) + G n := by rw [ih.2.2.1, ih.1]
            _ = G (n + 4) := (hGrec n).symm
            _ = G (n + 1 + 3) := by ring_nf
    exact (hblock k).1
  intro m
  calc
    D m = G m := hDG m
    _ =
        a * (Real.sqrt Real.goldenRatio) ^ m +
          b * (-Real.sqrt Real.goldenRatio) ^ m +
            (Real.sqrt Real.goldenRatio)⁻¹ ^ m *
              (c * Real.cos (Real.pi * (m : ℝ) / 2) +
                d * Real.sin (Real.pi * (m : ℝ) / 2)) := by
      rfl

end Omega.POM
