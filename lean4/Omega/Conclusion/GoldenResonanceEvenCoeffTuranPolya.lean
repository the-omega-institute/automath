import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-golden-resonance-even-coeff-turan-polya`. -/
theorem paper_conclusion_golden_resonance_even_coeff_turan_polya (b : Nat -> Real)
    (toeplitzFiniteMinorsNonnegative logStrictConcave : Prop)
    (hpf : toeplitzFiniteMinorsNonnegative) (hpos : ∀ r : Nat, 0 < b r)
    (hnewton : ∀ r : Nat, 1 ≤ r ->
      (((r : Real) + 1) / (r : Real)) * b (r - 1) * b (r + 1) ≤ b r ^ 2)
    (hlog : (∀ r : Nat, 1 ≤ r -> b (r - 1) * b (r + 1) < b r ^ 2) ->
      logStrictConcave) :
    toeplitzFiniteMinorsNonnegative ∧
      (∀ r : Nat, 1 ≤ r -> b (r - 1) * b (r + 1) < b r ^ 2) ∧
      logStrictConcave := by
  refine ⟨hpf, ?_, ?_⟩
  · intro r hr
    have hrposNat : 0 < r := Nat.succ_le_iff.mp hr
    have hrpos : (0 : Real) < r := by exact_mod_cast hrposNat
    have hfactor : 1 < (((r : Real) + 1) / (r : Real)) := by
      rw [lt_div_iff₀ hrpos]
      linarith
    have hprod_pos : 0 < b (r - 1) * b (r + 1) :=
      mul_pos (hpos (r - 1)) (hpos (r + 1))
    have hstrict :
        b (r - 1) * b (r + 1) <
          (((r : Real) + 1) / (r : Real)) * (b (r - 1) * b (r + 1)) := by
      nlinarith
    have hnewton_r := hnewton r hr
    nlinarith
  · exact hlog (by
      intro r hr
      have hrposNat : 0 < r := Nat.succ_le_iff.mp hr
      have hrpos : (0 : Real) < r := by exact_mod_cast hrposNat
      have hfactor : 1 < (((r : Real) + 1) / (r : Real)) := by
        rw [lt_div_iff₀ hrpos]
        linarith
      have hprod_pos : 0 < b (r - 1) * b (r + 1) :=
        mul_pos (hpos (r - 1)) (hpos (r + 1))
      have hstrict :
          b (r - 1) * b (r + 1) <
            (((r : Real) + 1) / (r : Real)) * (b (r - 1) * b (r + 1)) := by
        nlinarith
      have hnewton_r := hnewton r hr
      nlinarith)

end Omega.Conclusion
