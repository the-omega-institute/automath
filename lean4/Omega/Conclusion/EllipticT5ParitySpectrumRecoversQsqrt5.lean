import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-elliptic-t5-parity-spectrum-recovers-qsqrt5`. -/
theorem paper_conclusion_elliptic_t5_parity_spectrum_recovers_qsqrt5 (Podd Pinert : Set ℕ)
    (density : Set ℕ → ℝ) (hParity : Podd = Pinert)
    (hDensity : density Pinert = (1 : ℝ) / 2) :
    Podd = Pinert ∧ density Podd = (1 : ℝ) / 2 := by
  constructor
  · exact hParity
  · simpa [hParity] using hDensity

end Omega.Conclusion
