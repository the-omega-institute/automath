import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

/-- Paper label: `thm:leyang-lissajous-immersion-criterion`.
With both frequencies positive, the explicit derivative vector of the Lee--Yang/Lissajous
parametrization vanishes simultaneously exactly for the gcd-controlled phase lattice. -/
theorem paper_leyang_lissajous_immersion_criterion
    (a b : ℕ) (δ : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∃ t : ℝ,
      -(a : ℝ) * Real.sin ((a : ℝ) * t + δ) = 0 ∧
        -(b : ℝ) * Real.sin ((b : ℝ) * t) = 0) ↔
      ∃ n : ℤ, δ = ((((Nat.gcd a b : ℤ) * n : ℤ) : ℝ) * Real.pi) / b := by
  have ha0 : (a : ℝ) ≠ 0 := by positivity
  have hb0 : (b : ℝ) ≠ 0 := by positivity
  constructor
  · rintro ⟨t, hx, hy⟩
    have hsinx : Real.sin ((a : ℝ) * t + δ) = 0 := by
      have hx' : (a : ℝ) * Real.sin ((a : ℝ) * t + δ) = 0 := by linarith
      rcases mul_eq_zero.mp hx' with hzero | hzero
      · exact False.elim (ha0 hzero)
      · exact hzero
    have hsiny : Real.sin ((b : ℝ) * t) = 0 := by
      have hy' : (b : ℝ) * Real.sin ((b : ℝ) * t) = 0 := by linarith
      rcases mul_eq_zero.mp hy' with hzero | hzero
      · exact False.elim (hb0 hzero)
      · exact hzero
    rcases (Real.sin_eq_zero_iff.mp hsinx) with ⟨k, hk⟩
    rcases (Real.sin_eq_zero_iff.mp hsiny) with ⟨l, hl⟩
    have hdelta :
        δ = ((((k * b - a * l : ℤ) : ℝ) * Real.pi) / b) := by
      apply (eq_div_iff hb0).2
      calc
        δ * (b : ℝ)
            = ((a : ℝ) * t + δ) * (b : ℝ) - (a : ℝ) * ((b : ℝ) * t) := by ring
        _ = ((k : ℝ) * Real.pi) * (b : ℝ) - (a : ℝ) * ((l : ℝ) * Real.pi) := by
              rw [hk, hl]
        _ = (((k * b - a * l : ℤ) : ℝ) * Real.pi) := by
              push_cast
              ring
    have hga : (Nat.gcd a b : ℤ) ∣ (a : ℤ) := by
      exact_mod_cast Nat.gcd_dvd_left a b
    have hgb : (Nat.gcd a b : ℤ) ∣ (b : ℤ) := by
      exact_mod_cast Nat.gcd_dvd_right a b
    have hnum_dvd : (Nat.gcd a b : ℤ) ∣ (k * b - a * l : ℤ) := by
      rcases hga with ⟨a', ha'⟩
      rcases hgb with ⟨b', hb'⟩
      refine ⟨k * b' - a' * l, ?_⟩
      rw [ha', hb']
      ring
    rcases hnum_dvd with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [hdelta, hn]
  · rintro ⟨n, hδ⟩
    let g : ℤ := Nat.gcd a b
    let u : ℤ := Nat.gcdA a b
    let v : ℤ := Nat.gcdB a b
    let l : ℤ := -(u * n)
    let k : ℤ := v * n
    have hbez : g = a * u + b * v := by
      simpa [g, u, v] using (Nat.gcd_eq_gcd_ab a b)
    have hnum : k * b - a * l = g * n := by
      dsimp [k, l]
      calc
        v * n * ↑b - ↑a * -(u * n) = (↑a * u + ↑b * v) * n := by ring
        _ = g * n := by rw [hbez]
    have hnum' : (a : ℤ) * l + g * n = k * b := by
      calc
        (a : ℤ) * l + g * n = (a : ℤ) * l + (k * b - a * l) := by rw [hnum]
        _ = k * b := by ring
    have harg :
        (a : ℝ) * ((l : ℝ) * Real.pi / b) + δ = (k : ℝ) * Real.pi := by
      calc
        (a : ℝ) * ((l : ℝ) * Real.pi / b) + δ
            = (a : ℝ) * ((l : ℝ) * Real.pi / b) + (((g * n : ℤ) : ℝ) * Real.pi) / b := by
                rw [hδ]
        _ = ((((a : ℤ) * l + g * n : ℤ) : ℝ) * Real.pi) / b := by
              push_cast
              ring
        _ = ((((k * b : ℤ) : ℝ) * Real.pi) / b) := by rw [hnum']
        _ = (((k : ℝ) * (b : ℝ)) * Real.pi) / b := by
              push_cast
              ring
        _ = (k : ℝ) * Real.pi := by
              field_simp [hb0]
    refine ⟨(l : ℝ) * Real.pi / b, ?_, ?_⟩
    · have hsin : Real.sin ((k : ℝ) * Real.pi) = 0 := by
        exact (Real.sin_eq_zero_iff).2 ⟨k, rfl⟩
      have hsinx : Real.sin ((a : ℝ) * ((l : ℝ) * Real.pi / b) + δ) = 0 := by
        simp [harg, hsin]
      rw [hsinx]
      ring
    · have hargy : (b : ℝ) * ((l : ℝ) * Real.pi / b) = (l : ℝ) * Real.pi := by
        field_simp [hb0]
      have hsiny : Real.sin ((b : ℝ) * ((l : ℝ) * Real.pi / b)) = 0 := by
        simp [hargy]
      rw [hsiny]
      ring

end Omega.UnitCirclePhaseArithmetic
