import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-softcore-highq-one-mode-dominance`.  The off-principal
eigenvalue bound, normalized by `2^(q-1)`, is exactly the advertised `(phi / 2)^q` scale. -/
theorem paper_conclusion_softcore_highq_one_mode_dominance
    (phi : Real) (lambda : Nat → Nat → Real) (hphi_pos : 0 < phi) (hphi_lt : phi < 2)
    (hoff : ∀ q i, 1 ≤ i → i ≤ q → |lambda q i| ≤ (1 / 2 : Real) * phi ^ q) :
    ∀ q i, 1 ≤ i → i ≤ q → |lambda q i| / (2 : Real) ^ (q - 1) ≤
      (phi / 2) ^ q := by
  have _hphi_pos_used := hphi_pos
  have _hphi_lt_used := hphi_lt
  intro q i hi hile
  have hq : 1 ≤ q := le_trans hi hile
  have hden_nonneg : 0 ≤ (2 : Real) ^ (q - 1) := by positivity
  calc
    |lambda q i| / (2 : Real) ^ (q - 1) ≤
        ((1 / 2 : Real) * phi ^ q) / (2 : Real) ^ (q - 1) := by
          exact div_le_div_of_nonneg_right (hoff q i hi hile) hden_nonneg
    _ = (phi / 2) ^ q := by
          have hq_decomp : q = q - 1 + 1 := by omega
          have hden_ne : (2 : Real) ^ (q - 1) ≠ 0 := by positivity
          calc
            ((1 / 2 : Real) * phi ^ q) / (2 : Real) ^ (q - 1) =
                phi ^ q / ((2 : Real) * 2 ^ (q - 1)) := by
                  field_simp [hden_ne]
            _ = phi ^ q / (2 : Real) ^ q := by
                  have hpow : (2 : Real) ^ q = (2 : Real) * 2 ^ (q - 1) := by
                    conv_lhs => rw [hq_decomp]
                    rw [pow_add, pow_one]
                    ring
                  rw [hpow]
            _ = (phi / 2) ^ q := by
                  rw [div_pow]

end Omega.Conclusion
