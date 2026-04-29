import Mathlib.Tactic

namespace Omega.Conclusion

/-- The visible residue set `R₆`, represented by residues `0, ..., 20`. -/
abbrev conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_residue :=
  Fin 21

/-- The window-6 hidden multiplicity function on residues. -/
def conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_multiplicity
    (r : conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_residue) : ℕ :=
  if r.val ≤ 8 then 4 else if r.val ≤ 12 then 3 else 2

/-- The hidden excess `h(r) = d(r) - 1`. -/
def conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_hiddenExcess
    (r : conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_residue) : ℕ :=
  conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_multiplicity r - 1

/-- Exact-gcd conductor stratum inside residues modulo `21`. -/
def conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_stratum
    (δ : ℕ) :
    Finset conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_residue :=
  Finset.univ.filter fun r => Nat.gcd r.val 21 = δ

/-- The interval where `d = 4`. -/
def conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_intervalFour :
    Finset conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_residue :=
  Finset.univ.filter fun r => r.val ≤ 8

/-- The interval where `d = 3`. -/
def conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_intervalThree :
    Finset conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_residue :=
  Finset.univ.filter fun r => 9 ≤ r.val ∧ r.val ≤ 12

/-- The interval where `d = 2`. -/
def conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_intervalTwo :
    Finset conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_residue :=
  Finset.univ.filter fun r => 13 ≤ r.val

/-- Number of residues in a stratum and one multiplicity interval. -/
def conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_intervalCount
    (δ : ℕ)
    (I : Finset conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_residue) :
    ℕ :=
  ((conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_stratum δ) ∩ I).card

/-- Total hidden multiplicity on an exact-gcd stratum. -/
def conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_multiplicitySum
    (δ : ℕ) : ℕ :=
  (conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_stratum δ).sum
    conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_multiplicity

/-- Total hidden excess on an exact-gcd stratum. -/
def conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_hiddenExcessSum
    (δ : ℕ) : ℕ :=
  (conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_stratum δ).sum
    conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_hiddenExcess

/-- Concrete paper-facing statement: the explicit window-6 multiplicity histogram has average
`d = 3` and average hidden excess `h = 2` on each nonzero exact-gcd stratum, while `d(0)=4`. -/
def conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_statement : Prop :=
  (∀ r : conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_residue,
    (r.val ≤ 8 →
      conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_multiplicity r = 4) ∧
      (9 ≤ r.val → r.val ≤ 12 →
        conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_multiplicity r = 3) ∧
      (13 ≤ r.val →
        conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_multiplicity r = 2)) ∧
    conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_multiplicity 0 = 4 ∧
    conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_hiddenExcess 0 = 3 ∧
    (conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_stratum 1).card = 12 ∧
    (conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_stratum 3).card = 6 ∧
    (conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_stratum 7).card = 2 ∧
    (conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_stratum 21).card = 1 ∧
    conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_intervalCount 1
      conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_intervalFour = 5 ∧
    conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_intervalCount 1
      conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_intervalThree = 2 ∧
    conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_intervalCount 1
      conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_intervalTwo = 5 ∧
    conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_intervalCount 3
      conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_intervalFour = 2 ∧
    conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_intervalCount 3
      conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_intervalThree = 2 ∧
    conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_intervalCount 3
      conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_intervalTwo = 2 ∧
    conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_intervalCount 7
      conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_intervalFour = 1 ∧
    conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_intervalCount 7
      conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_intervalThree = 0 ∧
    conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_intervalCount 7
      conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_intervalTwo = 1 ∧
    conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_multiplicitySum 1 =
      3 * (conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_stratum 1).card ∧
    conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_multiplicitySum 3 =
      3 * (conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_stratum 3).card ∧
    conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_multiplicitySum 7 =
      3 * (conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_stratum 7).card ∧
    conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_hiddenExcessSum 1 =
      2 * (conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_stratum 1).card ∧
    conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_hiddenExcessSum 3 =
      2 * (conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_stratum 3).card ∧
    conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_hiddenExcessSum 7 =
      2 * (conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_stratum 7).card

/-- Paper label:
`thm:conclusion-window6-hidden-multiplicity-neutrality-on-nonzero-strata`. -/
theorem paper_conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata :
    conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_statement := by
  unfold conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_statement
  constructor
  · intro r
    fin_cases r <;>
      simp [conclusion_window6_hidden_multiplicity_neutrality_on_nonzero_strata_multiplicity]
  repeat' constructor <;> decide

end Omega.Conclusion
