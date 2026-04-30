import Mathlib.Tactic

namespace Omega.Conclusion

/-- Two positive atoms, `2 < 3`, with unit weights give a finite positive atomic spectrum. -/
noncomputable def conclusion_fixedresolution_moment_ratio_topgap_moment (q : ℕ) : ℝ :=
  (2 : ℝ) ^ q + (3 : ℝ) ^ q

/-- Adjacent moment ratio for the concrete two-atom spectrum. -/
noncomputable def conclusion_fixedresolution_moment_ratio_topgap_ratio (q : ℕ) : ℝ :=
  conclusion_fixedresolution_moment_ratio_topgap_moment (q + 1) /
    conclusion_fixedresolution_moment_ratio_topgap_moment q

/-- Concrete moment-ratio top-gap package for the two-atom positive spectrum `{2, 3}`. -/
noncomputable def conclusion_fixedresolution_moment_ratio_topgap_statement : Prop :=
  (∀ q : ℕ,
      2 < conclusion_fixedresolution_moment_ratio_topgap_ratio q ∧
        conclusion_fixedresolution_moment_ratio_topgap_ratio q < 3 ∧
          conclusion_fixedresolution_moment_ratio_topgap_ratio q ≤
            conclusion_fixedresolution_moment_ratio_topgap_ratio (q + 1)) ∧
    (∀ q : ℕ,
      conclusion_fixedresolution_moment_ratio_topgap_ratio q =
        ((2 : ℝ) ^ q / conclusion_fixedresolution_moment_ratio_topgap_moment q) * 2 +
          ((3 : ℝ) ^ q / conclusion_fixedresolution_moment_ratio_topgap_moment q) * 3) ∧
      ∀ q : ℕ,
        3 - conclusion_fixedresolution_moment_ratio_topgap_ratio q =
          (2 : ℝ) ^ q / conclusion_fixedresolution_moment_ratio_topgap_moment q

private lemma conclusion_fixedresolution_moment_ratio_topgap_moment_pos (q : ℕ) :
    0 < conclusion_fixedresolution_moment_ratio_topgap_moment q := by
  unfold conclusion_fixedresolution_moment_ratio_topgap_moment
  positivity

private lemma conclusion_fixedresolution_moment_ratio_topgap_pow2_pos (q : ℕ) :
    0 < (2 : ℝ) ^ q := by
  positivity

private lemma conclusion_fixedresolution_moment_ratio_topgap_pow3_pos (q : ℕ) :
    0 < (3 : ℝ) ^ q := by
  positivity

/-- Paper label: `thm:conclusion-fixedresolution-moment-ratio-topgap`. -/
theorem paper_conclusion_fixedresolution_moment_ratio_topgap :
    conclusion_fixedresolution_moment_ratio_topgap_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro q
    let a : ℝ := (2 : ℝ) ^ q
    let b : ℝ := (3 : ℝ) ^ q
    have ha : 0 < a := by
      dsimp [a]
      positivity
    have hb : 0 < b := by
      dsimp [b]
      positivity
    have hab : 0 < a + b := add_pos ha hb
    have hnextden : 0 < 2 * a + 3 * b := by nlinarith
    have hratio :
        conclusion_fixedresolution_moment_ratio_topgap_ratio q = (2 * a + 3 * b) / (a + b) := by
      simp [conclusion_fixedresolution_moment_ratio_topgap_ratio,
        conclusion_fixedresolution_moment_ratio_topgap_moment, a, b, pow_succ]
      ring_nf
    have hratio_next :
        conclusion_fixedresolution_moment_ratio_topgap_ratio (q + 1) =
          (4 * a + 9 * b) / (2 * a + 3 * b) := by
      simp [conclusion_fixedresolution_moment_ratio_topgap_ratio,
        conclusion_fixedresolution_moment_ratio_topgap_moment, a, b, pow_succ]
      ring_nf
    refine ⟨?_, ?_, ?_⟩
    · rw [hratio]
      rw [lt_div_iff₀ hab]
      nlinarith
    · rw [hratio]
      rw [div_lt_iff₀ hab]
      nlinarith
    · rw [hratio, hratio_next]
      rw [div_le_div_iff₀ hab hnextden]
      nlinarith
  · intro q
    have hm :=
      ne_of_gt (conclusion_fixedresolution_moment_ratio_topgap_moment_pos q)
    unfold conclusion_fixedresolution_moment_ratio_topgap_ratio
      conclusion_fixedresolution_moment_ratio_topgap_moment
    field_simp [hm, pow_succ]
    ring
  · intro q
    have hm :=
      ne_of_gt (conclusion_fixedresolution_moment_ratio_topgap_moment_pos q)
    unfold conclusion_fixedresolution_moment_ratio_topgap_ratio
      conclusion_fixedresolution_moment_ratio_topgap_moment
    field_simp [hm, pow_succ]
    ring

end Omega.Conclusion
