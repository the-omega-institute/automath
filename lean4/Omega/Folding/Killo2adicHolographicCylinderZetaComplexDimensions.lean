import Mathlib
import Omega.Folding.Killo2adicHolographicAttractorDimension

namespace Omega.Folding

open scoped Topology

noncomputable section

/-- The logarithmic scale factor of a depth-`L` dyadic cylinder. -/
noncomputable def killo_2adic_holographic_cylinder_zeta_complex_dimensions_scaleLog (L : ℕ) : ℝ :=
  (L : ℝ) * Real.log 2

/-- The geometric ratio attached to the constant-`q` cylinder zeta model. -/
noncomputable def killo_2adic_holographic_cylinder_zeta_complex_dimensions_ratio
    (L q : ℕ) (s : ℂ) : ℂ :=
  (q : ℂ) *
    Complex.exp
      (-s * (killo_2adic_holographic_cylinder_zeta_complex_dimensions_scaleLog L : ℂ))

/-- The cylinder zeta series in the constant-branch holographic address model. -/
noncomputable def killo_2adic_holographic_cylinder_zeta_complex_dimensions_series
    (L q : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  killo_2adic_holographic_cylinder_zeta_complex_dimensions_ratio L q s ^ n

/-- The vertical lattice solving `q * 2^(-L s) = 1` in the chosen branch model. -/
noncomputable def killo_2adic_holographic_cylinder_zeta_complex_dimensions_point
    (L q : ℕ) (k : ℤ) : ℂ :=
  (((Real.log q : ℝ) : ℂ) - (k : ℂ) * (2 * Real.pi * Complex.I)) /
    (killo_2adic_holographic_cylinder_zeta_complex_dimensions_scaleLog L : ℂ)

/-- Paper-facing package: prefix counts are exactly `q^n`, the cylinder zeta series is geometric on
the convergence half-plane, and the explicit vertical lattice solves the pole equation. -/
def killo_2adic_holographic_cylinder_zeta_complex_dimensions_statement : Prop :=
  ∀ {L q : ℕ}, 0 < L → 0 < q → q ≤ 2 ^ L →
    (∀ n : ℕ, (killoPrefixImage (2 ^ L) q n).card = q ^ n) ∧
      (∀ s : ℂ,
        ‖killo_2adic_holographic_cylinder_zeta_complex_dimensions_ratio L q s‖ < 1 →
          Summable (killo_2adic_holographic_cylinder_zeta_complex_dimensions_series L q s) ∧
            tsum (killo_2adic_holographic_cylinder_zeta_complex_dimensions_series L q s) =
              1 /
                (1 -
                  killo_2adic_holographic_cylinder_zeta_complex_dimensions_ratio L q s)) ∧
      ∀ k : ℤ,
        killo_2adic_holographic_cylinder_zeta_complex_dimensions_ratio L q
            (killo_2adic_holographic_cylinder_zeta_complex_dimensions_point L q k) =
          1

lemma killo_2adic_holographic_cylinder_zeta_complex_dimensions_geometric_closedForm
    {L q : ℕ} {s : ℂ}
    (hs :
      ‖killo_2adic_holographic_cylinder_zeta_complex_dimensions_ratio L q s‖ < 1) :
    Summable (killo_2adic_holographic_cylinder_zeta_complex_dimensions_series L q s) ∧
      tsum (killo_2adic_holographic_cylinder_zeta_complex_dimensions_series L q s) =
        1 / (1 - killo_2adic_holographic_cylinder_zeta_complex_dimensions_ratio L q s) := by
  refine ⟨?_, ?_⟩
  · change Summable
        (fun n : ℕ => killo_2adic_holographic_cylinder_zeta_complex_dimensions_ratio L q s ^ n)
    exact summable_geometric_of_norm_lt_one hs
  · change
      tsum (fun n : ℕ => killo_2adic_holographic_cylinder_zeta_complex_dimensions_ratio L q s ^ n) =
        1 / (1 - killo_2adic_holographic_cylinder_zeta_complex_dimensions_ratio L q s)
    simpa [one_div] using
      (tsum_geometric_of_norm_lt_one
        (ξ := killo_2adic_holographic_cylinder_zeta_complex_dimensions_ratio L q s) hs)

lemma killo_2adic_holographic_cylinder_zeta_complex_dimensions_ratio_point
    {L q : ℕ} (hL : 0 < L) (hq : 0 < q) (k : ℤ) :
    killo_2adic_holographic_cylinder_zeta_complex_dimensions_ratio L q
        (killo_2adic_holographic_cylinder_zeta_complex_dimensions_point L q k) =
      1 := by
  have hlog2 : 0 < Real.log (2 : ℝ) := by
    have htwo : (1 : ℝ) < 2 := by norm_num
    simpa using Real.log_pos htwo
  have hLreal : 0 < (L : ℝ) := by
    exact_mod_cast hL
  have hscale_pos :
      0 <
        killo_2adic_holographic_cylinder_zeta_complex_dimensions_scaleLog L := by
    unfold killo_2adic_holographic_cylinder_zeta_complex_dimensions_scaleLog
    exact mul_pos hLreal hlog2
  have hscale :
      (killo_2adic_holographic_cylinder_zeta_complex_dimensions_scaleLog L : ℂ) ≠ 0 := by
    exact_mod_cast hscale_pos.ne'
  have hqreal : 0 < (q : ℝ) := by
    exact_mod_cast hq
  have hqcomplex : (q : ℂ) ≠ 0 := by
    exact_mod_cast hq.ne'
  have hlogq : Complex.log (q : ℂ) = (Real.log q : ℂ) := by
    simp [Complex.ofReal_log (le_of_lt hqreal)]
  have hexp_qinv : Complex.exp (-((Real.log q : ℝ) : ℂ)) = (q : ℂ)⁻¹ := by
    rw [← hlogq, Complex.exp_neg, Complex.exp_log hqcomplex]
  have hexponent :
      -(killo_2adic_holographic_cylinder_zeta_complex_dimensions_point L q k) *
          (killo_2adic_holographic_cylinder_zeta_complex_dimensions_scaleLog L : ℂ) =
        -((Real.log q : ℝ) : ℂ) + (k : ℂ) * (2 * Real.pi * Complex.I) := by
    have hmul :
        killo_2adic_holographic_cylinder_zeta_complex_dimensions_point L q k *
            (killo_2adic_holographic_cylinder_zeta_complex_dimensions_scaleLog L : ℂ) =
          ((Real.log q : ℝ) : ℂ) - (k : ℂ) * (2 * Real.pi * Complex.I) := by
      simpa [killo_2adic_holographic_cylinder_zeta_complex_dimensions_point] using
        (div_mul_cancel₀
          (((Real.log q : ℝ) : ℂ) - (k : ℂ) * (2 * Real.pi * Complex.I)) hscale)
    have := congrArg Neg.neg hmul
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
      mul_assoc] using this
  unfold killo_2adic_holographic_cylinder_zeta_complex_dimensions_ratio
  rw [hexponent, Complex.exp_add, hexp_qinv, Complex.exp_int_mul_two_pi_mul_I]
  simp [hqcomplex]

/-- Paper label: `thm:killo-2adic-holographic-cylinder-zeta-complex-dimensions`. Reusing the
existing exact prefix-count package, the constant-`q` cylinder zeta function is a geometric series
with the displayed closed form on `‖q * 2^{-Ls}‖ < 1`, and the explicit vertical lattice solves
the pole equation. -/
theorem paper_killo_2adic_holographic_cylinder_zeta_complex_dimensions :
    killo_2adic_holographic_cylinder_zeta_complex_dimensions_statement := by
  intro L q hL hq hqL
  have hB : 1 < 2 ^ L := by
    cases L with
    | zero => cases Nat.lt_asymm hL hL
    | succ n => simp
  have hprefix :=
    paper_killo_2adic_holographic_attractor_dimension (B := 2 ^ L) (q := q) hB hq hqL
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact hprefix.1 n
  · intro s hs
    exact killo_2adic_holographic_cylinder_zeta_complex_dimensions_geometric_closedForm hs
  · intro k
    exact killo_2adic_holographic_cylinder_zeta_complex_dimensions_ratio_point hL hq k

end

end Omega.Folding
