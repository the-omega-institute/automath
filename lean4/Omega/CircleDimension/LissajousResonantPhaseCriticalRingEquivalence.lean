import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Omega.CircleDimension

lemma lissajous_resonant_phase_reflected_congruence (a b : ℕ) (δ : ℝ) :
    (∃ M N : ℤ, δ = Real.pi * ((M : ℝ) - (a : ℝ) / (b : ℝ) * (N : ℝ))) ↔
      (∃ M N : ℤ, δ = Real.pi * ((M : ℝ) + (a : ℝ) / (b : ℝ) * (N : ℝ))) := by
  constructor
  · rintro ⟨M, N, hδ⟩
    refine ⟨M, -N, ?_⟩
    simpa using hδ
  · rintro ⟨M, N, hδ⟩
    refine ⟨M, -N, ?_⟩
    simpa using hδ

/-- Paper label: `prop:cdim-lissajous-resonant-phase-critical-ring-equivalence`. -/
theorem paper_cdim_lissajous_resonant_phase_critical_ring_equivalence
    (a b : ℕ) (hb : 0 < b) (δ : ℝ) :
    (∃ M N : ℤ, δ = Real.pi * ((M : ℝ) - (a : ℝ) / (b : ℝ) * (N : ℝ))) ↔
      (∃ t : ℝ, Real.sin ((a : ℝ) * t + δ) = 0 ∧ Real.sin ((b : ℝ) * t) = 0) := by
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  constructor
  · rintro ⟨M, N, hδ⟩
    refine ⟨(N : ℝ) * Real.pi / (b : ℝ), ?_, ?_⟩
    · have ht : (a : ℝ) * ((N : ℝ) * Real.pi / (b : ℝ)) + δ = (M : ℝ) * Real.pi := by
        rw [hδ]
        field_simp [hb0]
        ring
      rw [ht, Real.sin_int_mul_pi]
    · have ht : (b : ℝ) * ((N : ℝ) * Real.pi / (b : ℝ)) = (N : ℝ) * Real.pi := by
        field_simp [hb0]
      rw [ht, Real.sin_int_mul_pi]
  · rintro ⟨t, hsinA, hsinB⟩
    rcases (Real.sin_eq_zero_iff.mp hsinA) with ⟨M, hM⟩
    rcases (Real.sin_eq_zero_iff.mp hsinB) with ⟨N, hN⟩
    have ht : t = (N : ℝ) * Real.pi / (b : ℝ) := by
      apply (eq_div_iff hb0).2
      simpa [mul_comm, mul_left_comm, mul_assoc] using hN.symm
    refine ⟨M, N, ?_⟩
    calc
      δ = (M : ℝ) * Real.pi - (a : ℝ) * t := by linarith
      _ = (M : ℝ) * Real.pi - (a : ℝ) * ((N : ℝ) * Real.pi / (b : ℝ)) := by rw [ht]
      _ = Real.pi * ((M : ℝ) - (a : ℝ) / (b : ℝ) * (N : ℝ)) := by
        field_simp [hb0]

end Omega.CircleDimension
