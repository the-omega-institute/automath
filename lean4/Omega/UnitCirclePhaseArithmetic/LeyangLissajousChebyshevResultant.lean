import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

/-- The `x`-coordinate of the phase-shifted Lee--Yang Lissajous parametrization. -/
noncomputable def leyangLissajousX (a : ℕ) (t δ : ℝ) : ℝ :=
  Real.cos ((a : ℝ) * t + δ)

/-- The `y`-coordinate of the phase-shifted Lee--Yang Lissajous parametrization. -/
noncomputable def leyangLissajousY (b : ℕ) (t : ℝ) : ℝ :=
  Real.cos ((b : ℝ) * t)

/-- The second-kind Chebyshev channel evaluated through the standard sine quotient, with the
removable singularity at `sin θ = 0` filled by `0`. -/
noncomputable def leyangChebyshevUValue (n : ℕ) (θ : ℝ) : ℝ :=
  if _h : Real.sin θ = 0 then 0 else Real.sin (((n + 1 : ℕ) : ℝ) * θ) / Real.sin θ

private lemma leyangChebyshevUValue_mul_sin (n : ℕ) (θ : ℝ) (h : Real.sin θ ≠ 0) :
    leyangChebyshevUValue n θ * Real.sin θ = Real.sin (((n + 1 : ℕ) : ℝ) * θ) := by
  rw [leyangChebyshevUValue, dif_neg h]
  field_simp [h]

/-- Paper-facing Lee--Yang/Chebyshev resultant identity for the phase-shifted Lissajous
parametrization, together with the inverse-square Lee--Yang coordinates on the punctured locus.
    thm:leyang-lissajous-chebyshev-resultant -/
theorem paper_leyang_lissajous_chebyshev_resultant (a b : ℕ) (t δ : ℝ)
    (hb : 1 ≤ b) (hθ : Real.sin ((a : ℝ) * t + δ) ≠ 0) :
    let θ := (a : ℝ) * t + δ
    let x := leyangLissajousX a t δ
    let y := leyangLissajousY b t
    let t_x := -(1 / (4 * x ^ 2))
    let t_y := -(1 / (4 * y ^ 2))
    (Real.cos ((a : ℝ) * ((b : ℝ) * t)) - Real.cos ((b : ℝ) * θ) * Real.cos ((b : ℝ) * δ)) ^ 2 =
        (1 - x ^ 2) * (leyangChebyshevUValue (b - 1) θ) ^ 2 * Real.sin ((b : ℝ) * δ) ^ 2 ∧
      ((x ≠ 0 ∧ y ≠ 0) → t_x ≤ -(1 / 4) ∧ t_y ≤ -(1 / 4)) := by
  intro θ x y t_x t_y
  have hθ' : Real.sin θ ≠ 0 := by
    simpa [θ] using hθ
  constructor
  · have hangle :
        (a : ℝ) * ((b : ℝ) * t) = (b : ℝ) * θ - (b : ℝ) * δ := by
      dsimp [θ]
      ring
    have hmain :
        Real.cos ((a : ℝ) * ((b : ℝ) * t)) -
            Real.cos ((b : ℝ) * θ) * Real.cos ((b : ℝ) * δ) =
          Real.sin ((b : ℝ) * θ) * Real.sin ((b : ℝ) * δ) := by
      calc
        Real.cos ((a : ℝ) * ((b : ℝ) * t)) -
            Real.cos ((b : ℝ) * θ) * Real.cos ((b : ℝ) * δ)
            =
              Real.cos ((b : ℝ) * θ - (b : ℝ) * δ) -
                Real.cos ((b : ℝ) * θ) * Real.cos ((b : ℝ) * δ) := by rw [hangle]
        _ = Real.sin ((b : ℝ) * θ) * Real.sin ((b : ℝ) * δ) := by
          rw [Real.cos_sub]
          ring
    have hsine :
        Real.sin θ ^ 2 = 1 - x ^ 2 := by
      dsimp [x, leyangLissajousX]
      nlinarith [Real.sin_sq_add_cos_sq θ]
    have hu :
        leyangChebyshevUValue (b - 1) θ * Real.sin θ = Real.sin ((b : ℝ) * θ) := by
      simpa [Nat.sub_add_cancel hb] using leyangChebyshevUValue_mul_sin (b - 1) θ hθ'
    calc
      (Real.cos ((a : ℝ) * ((b : ℝ) * t)) - Real.cos ((b : ℝ) * θ) * Real.cos ((b : ℝ) * δ)) ^ 2
          = (Real.sin ((b : ℝ) * θ) * Real.sin ((b : ℝ) * δ)) ^ 2 := by rw [hmain]
      _ = Real.sin ((b : ℝ) * θ) ^ 2 * Real.sin ((b : ℝ) * δ) ^ 2 := by ring
      _ = ((leyangChebyshevUValue (b - 1) θ * Real.sin θ) ^ 2) *
            Real.sin ((b : ℝ) * δ) ^ 2 := by
            rw [hu]
      _ = (leyangChebyshevUValue (b - 1) θ) ^ 2 * Real.sin θ ^ 2 *
            Real.sin ((b : ℝ) * δ) ^ 2 := by ring
      _ = (leyangChebyshevUValue (b - 1) θ) ^ 2 * (1 - x ^ 2) *
            Real.sin ((b : ℝ) * δ) ^ 2 := by rw [hsine]
      _ = (1 - x ^ 2) * (leyangChebyshevUValue (b - 1) θ) ^ 2 *
            Real.sin ((b : ℝ) * δ) ^ 2 := by ring
  · rintro ⟨hx0, hy0⟩
    have hxsq_le : x ^ 2 ≤ 1 := by
      dsimp [x, leyangLissajousX]
      nlinarith [Real.sin_sq_add_cos_sq θ]
    have hysq_le : y ^ 2 ≤ 1 := by
      dsimp [y, leyangLissajousY]
      nlinarith [Real.sin_sq_add_cos_sq ((b : ℝ) * t)]
    have hxnum : x ^ 2 - 1 ≤ 0 := by linarith
    have hynum : y ^ 2 - 1 ≤ 0 := by linarith
    have hxden : 0 ≤ 4 * x ^ 2 := by positivity
    have hyden : 0 ≤ 4 * y ^ 2 := by positivity
    have hxfrac : (x ^ 2 - 1) / (4 * x ^ 2) ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg hxnum hxden
    have hyfrac : (y ^ 2 - 1) / (4 * y ^ 2) ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg hynum hyden
    have htx :
        -(1 / (4 * x ^ 2)) + 1 / 4 = (x ^ 2 - 1) / (4 * x ^ 2) := by
      field_simp [hx0]
      ring
    have hty :
        -(1 / (4 * y ^ 2)) + 1 / 4 = (y ^ 2 - 1) / (4 * y ^ 2) := by
      field_simp [hy0]
      ring
    constructor
    · dsimp [t_x]
      nlinarith [hxfrac, htx]
    · dsimp [t_y]
      nlinarith [hyfrac, hty]

end Omega.UnitCirclePhaseArithmetic
