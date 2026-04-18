import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic

namespace Omega.Conclusion

/-- `thm:conclusion-additive-scalar-procircle-obstruction` -/
theorem paper_conclusion_additive_scalar_procircle_obstruction
    (Dhat c0 : ENNReal) (D : ℕ → ENNReal) (hc0 : 0 < c0)
    (hlower : ∀ n : ℕ, (n : ENNReal) * c0 ≤ D n) (hupper : ∀ n : ℕ, D n ≤ Dhat) :
    Dhat = ⊤ := by
  by_cases hc0_top : c0 = ⊤
  · have htop_le : ⊤ ≤ Dhat := by
      simpa [hc0_top] using (le_trans (hlower 1) (hupper 1))
    exact top_le_iff.mp htop_le
  · by_contra hDhat_top
    have hc0_ne_zero : c0 ≠ 0 := ne_of_gt hc0
    have hc0_real_pos : 0 < c0.toReal := ENNReal.toReal_pos hc0_ne_zero hc0_top
    obtain ⟨n, hn⟩ := exists_nat_gt (Dhat.toReal / c0.toReal)
    have hbound :
        ((n : ENNReal) * c0).toReal ≤ Dhat.toReal :=
      ENNReal.toReal_mono hDhat_top (le_trans (hlower n) (hupper n))
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hbound
    have hn' : Dhat.toReal < (n : ℝ) * c0.toReal := by
      exact (div_lt_iff₀ hc0_real_pos).mp hn
    exact (not_lt_of_ge hbound) hn'

end Omega.Conclusion
