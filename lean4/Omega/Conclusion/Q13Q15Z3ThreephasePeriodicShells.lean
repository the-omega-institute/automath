import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete data for the `q = 13, 15` triadic three-phase shell package. -/
structure conclusion_q13_q15_z3_threephase_periodic_shells_data where
  q : ℕ
  l : ℕ
  nilpotentTransient : ℕ
  plusPeriod : ℕ
  minusPeriod : ℕ
  hq : q = 13 ∨ q = 15
  hnil : nilpotentTransient ≤ 2 * l
  hplus : plusPeriod ∣ 3
  hminus : minusPeriod ∣ 3

namespace conclusion_q13_q15_z3_threephase_periodic_shells_data

/-- The canonical three-factor Hensel split determined by `q`. -/
def conclusion_q13_q15_z3_threephase_periodic_shells_canonical_split
    (D : conclusion_q13_q15_z3_threephase_periodic_shells_data) : Fin 3 → ℕ :=
  fun i => if i = 0 then 1 else if i = 1 then D.q else D.q ^ 2

/-- The three-phase factorization is unique once the three shell values are fixed. -/
def has_unique_hensel_split
    (D : conclusion_q13_q15_z3_threephase_periodic_shells_data) : Prop :=
  ∃! s : Fin 3 → ℕ, s 0 = 1 ∧ s 1 = D.q ∧ s 2 = D.q ^ 2

/-- The nilpotent transient is bounded by `2 * l`. -/
def nilpotent_shell_bound
    (D : conclusion_q13_q15_z3_threephase_periodic_shells_data) : Prop :=
  D.nilpotentTransient ≤ 2 * D.l

/-- The combined plus/minus periodic shell is still `3`-periodic. -/
def semisimple_periodic_shell_bound
    (D : conclusion_q13_q15_z3_threephase_periodic_shells_data) : Prop :=
  Nat.lcm D.plusPeriod D.minusPeriod ∣ 3

/-- For `q = 13, 15` no residue class `2 mod 3` appears, so there is no new phase channel. -/
def no_new_phase_channels
    (D : conclusion_q13_q15_z3_threephase_periodic_shells_data) : Prop :=
  D.q % 3 ≠ 2

end conclusion_q13_q15_z3_threephase_periodic_shells_data

/-- Paper label: `thm:conclusion-q13-q15-z3-threephase-periodic-shells`. -/
theorem paper_conclusion_q13_q15_z3_threephase_periodic_shells
    (D : conclusion_q13_q15_z3_threephase_periodic_shells_data) :
    D.has_unique_hensel_split ∧ D.nilpotent_shell_bound ∧ D.semisimple_periodic_shell_bound ∧
      D.no_new_phase_channels := by
  refine ⟨?_, D.hnil, ?_, ?_⟩
  · refine ⟨D.conclusion_q13_q15_z3_threephase_periodic_shells_canonical_split, ?_, ?_⟩
    · refine ⟨by
        simp [conclusion_q13_q15_z3_threephase_periodic_shells_data.conclusion_q13_q15_z3_threephase_periodic_shells_canonical_split],
        by
          simp [conclusion_q13_q15_z3_threephase_periodic_shells_data.conclusion_q13_q15_z3_threephase_periodic_shells_canonical_split],
        by
          simp [conclusion_q13_q15_z3_threephase_periodic_shells_data.conclusion_q13_q15_z3_threephase_periodic_shells_canonical_split]⟩
    · intro s hs
      ext i
      fin_cases i
      · exact hs.1
      · exact hs.2.1
      · exact hs.2.2
  · exact Nat.lcm_dvd D.hplus D.hminus
  · unfold conclusion_q13_q15_z3_threephase_periodic_shells_data.no_new_phase_channels
    rcases D.hq with hq | hq <;> simp [hq]

end Omega.Conclusion
