import Mathlib.Tactic

namespace Omega.Conclusion

/-- If a left secant slope is bounded by the last adjacent slope, their weighted average is
bounded by that same adjacent slope. -/
lemma conclusion_discrete_q_fan_exposed_fan_of_pressure_secant_left_average
    {A L d : ℝ} (hd : 0 < d) (hA : A / d ≤ L) :
    (A + L) / (d + 1) ≤ L := by
  have hA' : A ≤ L * d := by
    rw [div_le_iff₀ hd] at hA
    exact hA
  have hd1 : 0 < d + 1 := by linarith
  rw [div_le_iff₀ hd1]
  nlinarith

/-- If a right secant slope is bounded below by the first adjacent slope, their weighted average
is bounded below by that same adjacent slope. -/
lemma conclusion_discrete_q_fan_exposed_fan_of_pressure_secant_right_average
    {R C d : ℝ} (hd : 0 < d) (hC : R ≤ C / d) :
    R ≤ (R + C) / (1 + d) := by
  have hC' : R * d ≤ C := by
    rw [le_div_iff₀ hd] at hC
    exact hC
  have hd1 : 0 < 1 + d := by linarith
  rw [le_div_iff₀ hd1]
  nlinarith

/-- Paper label: `thm:conclusion-discrete-q-fan-exposed-fan-of-pressure-secant`. -/
theorem paper_conclusion_discrete_q_fan_exposed_fan_of_pressure_secant
    (b : ℕ → ℝ) {Q q : ℕ} (γ : ℝ) (hQ : 4 ≤ Q) (hqlo : 3 ≤ q)
    (hqhi : q + 1 ≤ Q)
    (hconv : ∀ i j k, 2 ≤ i → i < j → j < k → k ≤ Q →
      (b j - b i) / ((j : ℝ) - i) ≤ (b k - b j) / ((k : ℝ) - j)) :
    ((∀ r, 2 ≤ r → r ≤ Q →
        ((r : ℝ) - 1) * γ - b r ≤ ((q : ℝ) - 1) * γ - b q) ↔
      b q - b (q - 1) ≤ γ ∧ γ ≤ b (q + 1) - b q) := by
  have _ : 4 ≤ Q := hQ
  constructor
  · intro hmax
    constructor
    · have hqpred2 : 2 ≤ q - 1 := by omega
      have hqpredQ : q - 1 ≤ Q := by omega
      have hleft :=
        hmax (q - 1) hqpred2 hqpredQ
      have hqpred_cast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
        norm_num [Nat.cast_sub (by omega : 1 ≤ q)]
      have hleft' :
          (((q : ℝ) - 1) - 1) * γ - b (q - 1) ≤
            ((q : ℝ) - 1) * γ - b q := by
        simpa [hqpred_cast] using hleft
      ring_nf at hleft'
      linarith
    · have hqnext2 : 2 ≤ q + 1 := by omega
      have hright :=
        hmax (q + 1) hqnext2 hqhi
      have hright' :
          (q : ℝ) * γ - b (q + 1) ≤ ((q : ℝ) - 1) * γ - b q := by
        simpa using hright
      ring_nf at hright'
      have hb : b (1 + q) = b (q + 1) := by rw [Nat.add_comm]
      linarith
  · rintro ⟨hleftSlope, hrightSlope⟩ r hr2 hrQ
    rcases lt_trichotomy r q with hrlt | rfl | hq_lt_r
    · have hden_pos : 0 < (q : ℝ) - (r : ℝ) := by
        have hcast : (r : ℝ) < (q : ℝ) := by exact_mod_cast hrlt
        linarith
      have hsec : (b q - b r) / ((q : ℝ) - r) ≤ γ := by
        by_cases hrpred : r = q - 1
        · subst r
          have hden : (q : ℝ) - ((q - 1 : ℕ) : ℝ) = 1 := by
            norm_num [Nat.cast_sub (by omega : 1 ≤ q)]
          simpa [hden] using hleftSlope
        · have hrltpred : r < q - 1 := by omega
          have hqpred_lt : q - 1 < q := by omega
          have hqQ : q ≤ Q := by omega
          have hmono :=
            hconv r (q - 1) q hr2 hrltpred hqpred_lt hqQ
          have hqpred_cast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
            norm_num [Nat.cast_sub (by omega : 1 ≤ q)]
          have hlast_den : (q : ℝ) - ((q - 1 : ℕ) : ℝ) = 1 := by
            norm_num [Nat.cast_sub (by omega : 1 ≤ q)]
          have hd : 0 < ((q - 1 : ℕ) : ℝ) - (r : ℝ) := by
            have hcast : (r : ℝ) < ((q - 1 : ℕ) : ℝ) := by exact_mod_cast hrltpred
            linarith
          have hmono' :
              (b (q - 1) - b r) / (((q - 1 : ℕ) : ℝ) - r) ≤
                b q - b (q - 1) := by
            simpa [hlast_den] using hmono
          have havg :=
            conclusion_discrete_q_fan_exposed_fan_of_pressure_secant_left_average
              (A := b (q - 1) - b r) (L := b q - b (q - 1))
              (d := ((q - 1 : ℕ) : ℝ) - r) hd hmono'
          have hden :
              (((q - 1 : ℕ) : ℝ) - (r : ℝ)) + 1 = (q : ℝ) - r := by
            nlinarith
          have hnum : b (q - 1) - b r + (b q - b (q - 1)) = b q - b r := by
            ring
          have hsec_le :
              (b q - b r) / ((q : ℝ) - r) ≤ b q - b (q - 1) := by
            simpa [hnum, hden] using havg
          exact le_trans hsec_le hleftSlope
      have hsec' : b q - b r ≤ γ * ((q : ℝ) - r) := by
        rwa [div_le_iff₀ hden_pos] at hsec
      nlinarith
    · simp
    · have hden_pos : 0 < (r : ℝ) - (q : ℝ) := by
        have hcast : (q : ℝ) < (r : ℝ) := by exact_mod_cast hq_lt_r
        linarith
      have hsec : γ ≤ (b r - b q) / ((r : ℝ) - q) := by
        by_cases hrnext : r = q + 1
        · subst r
          have hden : ((q + 1 : ℕ) : ℝ) - (q : ℝ) = 1 := by norm_num
          simpa [hden] using hrightSlope
        · have hnextlt : q + 1 < r := by omega
          have hq2 : 2 ≤ q := by omega
          have hq_lt_next : q < q + 1 := by omega
          have hmono :=
            hconv q (q + 1) r hq2 hq_lt_next hnextlt hrQ
          have hfirst_den : ((q + 1 : ℕ) : ℝ) - (q : ℝ) = 1 := by norm_num
          have hd : 0 < (r : ℝ) - ((q + 1 : ℕ) : ℝ) := by
            have hcast : ((q + 1 : ℕ) : ℝ) < (r : ℝ) := by exact_mod_cast hnextlt
            linarith
          have hmono' :
              b (q + 1) - b q ≤ (b r - b (q + 1)) /
                ((r : ℝ) - ((q + 1 : ℕ) : ℝ)) := by
            simpa [hfirst_den] using hmono
          have havg :=
            conclusion_discrete_q_fan_exposed_fan_of_pressure_secant_right_average
              (R := b (q + 1) - b q) (C := b r - b (q + 1))
              (d := (r : ℝ) - ((q + 1 : ℕ) : ℝ)) hd hmono'
          have hden :
              1 + ((r : ℝ) - ((q + 1 : ℕ) : ℝ)) = (r : ℝ) - q := by
            have hqnext_cast : ((q + 1 : ℕ) : ℝ) = (q : ℝ) + 1 := by norm_num
            linarith
          have hnum : b (q + 1) - b q + (b r - b (q + 1)) = b r - b q := by
            ring
          have hright_le :
              b (q + 1) - b q ≤ (b r - b q) / ((r : ℝ) - q) := by
            rw [← hden]
            simpa [hnum] using havg
          exact le_trans hrightSlope hright_le
      have hsec' : γ * ((r : ℝ) - q) ≤ b r - b q := by
        rwa [le_div_iff₀ hden_pos] at hsec
      nlinarith

end Omega.Conclusion
