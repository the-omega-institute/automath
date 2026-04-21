import Omega.CircleDimension.LissajousPhaseCirclePrimeLedgerKernel
import Omega.CircleDimension.RhodoneaSolenoidDesingularizedLift

namespace Real

/-- Local seed so the paper-facing theorem can use the requested `Real.re` notation. -/
def re (z : ℂ) : ℝ := Complex.re z

end Real

namespace Omega.CircleDimension

/-- Paper label: `cor:cdim-rational-character-projection-unifies-rose-lissajous`. The rhodonea
character average is the cosine gate on the common carrier phase, and taking real parts of the
phase-lift coordinates recovers the visible Lissajous orbit. -/
theorem paper_cdim_rational_character_projection_unifies_rose_lissajous
    (d n a b : ℕ) (hd : 0 < d) (hn : n < d) (δ t : ℝ) :
    ((Complex.exp ((((t + ((n : ℝ) / d) * t) : ℝ) : ℂ) * Complex.I) +
        Complex.exp ((((t - ((n : ℝ) / d) * t) : ℝ) : ℂ) * Complex.I)) / 2 =
      Complex.exp (((t : ℂ) * Complex.I)) * Real.cos (((n : ℝ) / d) * t)) ∧
      ((Real.re (Complex.exp ((((a : ℝ) * t + δ) : ℂ) * Complex.I)),
          Real.re (Complex.exp ((((b : ℝ) * t) : ℂ) * Complex.I))) =
        (Real.cos ((a : ℝ) * t + δ), Real.cos ((b : ℝ) * t))) := by
  have _ := hd
  have _ := hn
  constructor
  · let y : ℝ := ((n : ℝ) / d) * t
    have hplus : ((((t + y) : ℝ) : ℂ) * Complex.I) =
        ((t : ℂ) * Complex.I) + ((y : ℂ) * Complex.I) := by
      simp [y]
      ring
    have hminus : ((((t - y) : ℝ) : ℂ) * Complex.I) =
        ((t : ℂ) * Complex.I) + (-((y : ℂ) * Complex.I)) := by
      simp [y]
      ring
    have hcos :
        ((Complex.exp (((y : ℂ) * Complex.I)) + Complex.exp (-((y : ℂ) * Complex.I))) / 2) =
          Complex.cos y := by
      simp [Complex.cos]
    calc
      (Complex.exp ((((t + ((n : ℝ) / d) * t) : ℝ) : ℂ) * Complex.I) +
          Complex.exp ((((t - ((n : ℝ) / d) * t) : ℝ) : ℂ) * Complex.I)) / 2 =
          (Complex.exp (((t : ℂ) * Complex.I)) *
            (Complex.exp (((y : ℂ) * Complex.I)) + Complex.exp (-((y : ℂ) * Complex.I)))) / 2 := by
              rw [show (((t + ((n : ℝ) / d) * t) : ℝ) : ℂ) = ((t + y : ℝ) : ℂ) by simp [y],
                show (((t - ((n : ℝ) / d) * t) : ℝ) : ℂ) = ((t - y : ℝ) : ℂ) by simp [y]]
              rw [hplus, hminus, Complex.exp_add, Complex.exp_add]
              ring
      _ = Complex.exp (((t : ℂ) * Complex.I)) *
            ((Complex.exp (((y : ℂ) * Complex.I)) + Complex.exp (-((y : ℂ) * Complex.I))) / 2) := by
              ring
      _ = Complex.exp (((t : ℂ) * Complex.I)) * Complex.cos y := by
            rw [hcos]
      _ = Complex.exp (((t : ℂ) * Complex.I)) * Real.cos (((n : ℝ) / d) * t) := by
            simpa [y] using
              congrArg (fun z : ℂ => Complex.exp (((t : ℂ) * Complex.I)) * z)
                (Complex.ofReal_cos y).symm
  · ext <;> simp [Real.re]
    · simpa using (Complex.exp_ofReal_mul_I_re ((a : ℝ) * t + δ))
    · simpa using (Complex.exp_ofReal_mul_I_re ((b : ℝ) * t))

end Omega.CircleDimension
