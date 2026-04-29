import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-haar-zero-universality-does-not-force-amplitude-universality`. -/
theorem paper_conclusion_haar_zero_universality_does_not_force_amplitude_universality
    (HaarLimit : (ℕ → ℕ → ℤ) → Prop) (ampDist : (ℕ → ℤ) → (ℕ → ℤ) → ℝ)
    (universalAmplitude : Prop) (p0 : ℕ) (a b : ℤ) (q : ℕ → ℕ) (hab : a ≠ b)
    (huniv : ∀ c : ℤ,
      HaarLimit (fun N p => if p = p0 then c else if p = q N then 1 else 0))
    (hrigid : ∀ r s : ℕ → ℤ,
      Real.sqrt Real.pi * |((r p0 - s p0 : ℤ) : ℝ)| ≤ ampDist r s)
    (hcollapse : universalAmplitude → ∀ N,
      ampDist
          (fun p => if p = p0 then a else if p = q N then 1 else 0)
          (fun p => if p = p0 then b else if p = q N then 1 else 0) =
        0) :
    ¬ universalAmplitude := by
  intro hUniversal
  have _ :
      HaarLimit (fun N p => if p = p0 then a else if p = q N then 1 else 0) ∧
        HaarLimit (fun N p => if p = p0 then b else if p = q N then 1 else 0) :=
    ⟨huniv a, huniv b⟩
  have hle :
      Real.sqrt Real.pi * |((a - b : ℤ) : ℝ)| ≤
        ampDist
          (fun p => if p = p0 then a else if p = q 0 then 1 else 0)
          (fun p => if p = p0 then b else if p = q 0 then 1 else 0) := by
    simpa using
      hrigid
        (fun p => if p = p0 then a else if p = q 0 then 1 else 0)
        (fun p => if p = p0 then b else if p = q 0 then 1 else 0)
  rw [hcollapse hUniversal 0] at hle
  have hdiff_int : (a - b : ℤ) ≠ 0 := sub_ne_zero.mpr hab
  have hdiff_real : ((a - b : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast hdiff_int
  have hpos_abs : 0 < |((a - b : ℤ) : ℝ)| := abs_pos.mpr hdiff_real
  have hpos_sqrt : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hpos : 0 < Real.sqrt Real.pi * |((a - b : ℤ) : ℝ)| :=
    mul_pos hpos_sqrt hpos_abs
  linarith

end Omega.Conclusion
