import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.POM.MomentMod3TwoPhase

namespace Omega.POM

open scoped BigOperators

/-- The two resonant windows covered by the mod-`3` two-phase period package. -/
def pom_resonance_mod3_two_phase_period_q13_15_q : Fin 2 → ℕ
  | 0 => 13
  | 1 => 15

/-- Lucas-periodic binomial residue for the degree range needed here. -/
def pom_resonance_mod3_two_phase_period_q13_15_lucas_binomial_residue
    (n : ℕ) (j : ℕ) : ZMod 3 :=
  Nat.choose (n % 9) j

/-- The degree-`3` mod-`3` polynomial phase, represented in the Lucas-periodic binomial basis. -/
def pom_resonance_mod3_two_phase_period_q13_15_polynomial_phase
    (a : Fin 4 → ZMod 3) (n : ℕ) : ZMod 3 :=
  ∑ i : Fin 4, a i *
    pom_resonance_mod3_two_phase_period_q13_15_lucas_binomial_residue n i

/-- The degree-`4` alternating mod-`3` polynomial phase. -/
def pom_resonance_mod3_two_phase_period_q13_15_alternating_phase
    (b : Fin 5 → ZMod 3) (n : ℕ) : ZMod 3 :=
  (-1 : ZMod 3) ^ n * ∑ j : Fin 5, b j *
    pom_resonance_mod3_two_phase_period_q13_15_lucas_binomial_residue n j

/-- The packaged two-phase normal-form sequence for `q = 13, 15`. -/
def pom_resonance_mod3_two_phase_period_q13_15_sequence
    (q : Fin 2) (a : Fin 4 → ZMod 3) (b : Fin 5 → ZMod 3) (n : ℕ) : ZMod 3 :=
  pom_resonance_mod3_two_phase_period_q13_15_polynomial_phase a n +
    pom_resonance_mod3_two_phase_period_q13_15_alternating_phase b n +
      (0 : ZMod 3) * pom_resonance_mod3_two_phase_period_q13_15_q q

/-- Concrete statement for the `q = 13, 15` mod-`3` two-phase normal form and period bound. -/
def pom_resonance_mod3_two_phase_period_q13_15_statement : Prop :=
  (∀ a : Fin 4 → ℚ, ∀ b : Fin 5 → ℚ,
    ∃ sPos sNeg : ℕ → ℚ,
      (∀ n, pomMomentMod3ShiftedSequence a b n = sPos n + sNeg n) ∧
      IsBinomialPolynomialPhase sPos 1 3 ∧
      IsBinomialPolynomialPhase sNeg (-1) 4) ∧
    (∀ q : Fin 2, pom_resonance_mod3_two_phase_period_q13_15_q q = 13 ∨
      pom_resonance_mod3_two_phase_period_q13_15_q q = 15) ∧
    (∀ q : Fin 2, ∀ a : Fin 4 → ZMod 3, ∀ b : Fin 5 → ZMod 3,
      (∀ n,
        pom_resonance_mod3_two_phase_period_q13_15_sequence q a b n =
          pom_resonance_mod3_two_phase_period_q13_15_polynomial_phase a n +
            pom_resonance_mod3_two_phase_period_q13_15_alternating_phase b n) ∧
        ∀ n,
          pom_resonance_mod3_two_phase_period_q13_15_sequence q a b (n + 18) =
            pom_resonance_mod3_two_phase_period_q13_15_sequence q a b n)

private theorem pom_resonance_mod3_two_phase_period_q13_15_mod_nine (n : ℕ) :
    (n + 18) % 9 = n % 9 := by
  omega

private theorem pom_resonance_mod3_two_phase_period_q13_15_neg_one_pow_period
    (n : ℕ) : (-1 : ZMod 3) ^ (n + 18) = (-1 : ZMod 3) ^ n := by
  rw [pow_add]
  norm_num

/-- Paper label: `thm:pom-resonance-mod3-two-phase-period-q13-15`. -/
theorem paper_pom_resonance_mod3_two_phase_period_q13_15 :
    pom_resonance_mod3_two_phase_period_q13_15_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    exact paper_pom_moment_mod3_two_phase a b
  · intro q
    fin_cases q <;> simp [pom_resonance_mod3_two_phase_period_q13_15_q]
  · intro q a b
    refine ⟨?_, ?_⟩
    · intro n
      simp [pom_resonance_mod3_two_phase_period_q13_15_sequence]
    · intro n
      simp [pom_resonance_mod3_two_phase_period_q13_15_sequence,
        pom_resonance_mod3_two_phase_period_q13_15_polynomial_phase,
        pom_resonance_mod3_two_phase_period_q13_15_alternating_phase,
        pom_resonance_mod3_two_phase_period_q13_15_lucas_binomial_residue,
        pom_resonance_mod3_two_phase_period_q13_15_mod_nine n,
        pom_resonance_mod3_two_phase_period_q13_15_neg_one_pow_period n]

end Omega.POM
