import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-primeslice-optimal-implementation-schur-concavity`. -/
theorem paper_conclusion_primeslice_optimal_implementation_schur_concavity
    (B : ℕ) (phi : ℕ → ℝ)
    (hstep : ∀ r, 0 < r → r < B →
      phi (r + 1) - 2 * phi r + phi (r - 1) =
        Real.log (((B - r : ℕ) : ℝ) / ((B - r + 1 : ℕ) : ℝ))) :
    ∀ r, 0 < r → r < B → phi (r + 1) - 2 * phi r + phi (r - 1) < 0 := by
  intro r hr hlt
  rw [hstep r hr hlt]
  have hnum_pos_nat : 0 < B - r := Nat.sub_pos_of_lt hlt
  have hden_pos_nat : 0 < B - r + 1 := Nat.succ_pos (B - r)
  have hnum_pos : (0 : ℝ) < ((B - r : ℕ) : ℝ) := Nat.cast_pos.mpr hnum_pos_nat
  have hden_pos : (0 : ℝ) < ((B - r + 1 : ℕ) : ℝ) :=
    Nat.cast_pos.mpr hden_pos_nat
  have hnum_lt_den_nat : B - r < B - r + 1 := Nat.lt_succ_self (B - r)
  have hnum_lt_den : ((B - r : ℕ) : ℝ) < ((B - r + 1 : ℕ) : ℝ) := by
    exact_mod_cast hnum_lt_den_nat
  have hratio_pos :
      (0 : ℝ) < ((B - r : ℕ) : ℝ) / ((B - r + 1 : ℕ) : ℝ) :=
    div_pos hnum_pos hden_pos
  have hratio_lt_one :
      ((B - r : ℕ) : ℝ) / ((B - r + 1 : ℕ) : ℝ) < 1 :=
    (div_lt_one hden_pos).2 hnum_lt_den
  exact Real.log_neg hratio_pos hratio_lt_one

end Omega.Conclusion
