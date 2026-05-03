import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite residue-field data for the simultaneous Hankel deresonance union bound.  The
sets `badResidues r` are the residue classes where the `r`-th Hankel minor fails to attain its
tropical valuation, and `success_of_not_bad` records the valuation implication outside all bad
events. -/
structure conclusion_padic_hankel_simultaneous_deresonance_data where
  conclusion_padic_hankel_simultaneous_deresonance_q : ℕ
  conclusion_padic_hankel_simultaneous_deresonance_kappa : ℕ
  conclusion_padic_hankel_simultaneous_deresonance_badResidues :
    Fin conclusion_padic_hankel_simultaneous_deresonance_kappa →
      Finset (Fin conclusion_padic_hankel_simultaneous_deresonance_q)
  conclusion_padic_hankel_simultaneous_deresonance_perIndexBound :
    Fin conclusion_padic_hankel_simultaneous_deresonance_kappa → ℕ
  conclusion_padic_hankel_simultaneous_deresonance_valuation :
    Fin conclusion_padic_hankel_simultaneous_deresonance_kappa →
      Fin conclusion_padic_hankel_simultaneous_deresonance_q → ℤ
  conclusion_padic_hankel_simultaneous_deresonance_targetValuation :
    Fin conclusion_padic_hankel_simultaneous_deresonance_kappa → ℤ
  conclusion_padic_hankel_simultaneous_deresonance_badResidues_card_bound :
    ∀ r,
      (conclusion_padic_hankel_simultaneous_deresonance_badResidues r).card ≤
        conclusion_padic_hankel_simultaneous_deresonance_perIndexBound r
  conclusion_padic_hankel_simultaneous_deresonance_success_of_not_bad :
    ∀ u,
      (∀ r,
        u ∉ conclusion_padic_hankel_simultaneous_deresonance_badResidues r) →
        ∀ r,
          conclusion_padic_hankel_simultaneous_deresonance_valuation r u =
            conclusion_padic_hankel_simultaneous_deresonance_targetValuation r

namespace conclusion_padic_hankel_simultaneous_deresonance_data

/-- The finite union of all bad residues over the Hankel-minor tower. -/
def conclusion_padic_hankel_simultaneous_deresonance_badResidueUnion
    (D : conclusion_padic_hankel_simultaneous_deresonance_data) :
    Finset (Fin D.conclusion_padic_hankel_simultaneous_deresonance_q) :=
  (Finset.univ :
    Finset (Fin D.conclusion_padic_hankel_simultaneous_deresonance_kappa)).biUnion
    D.conclusion_padic_hankel_simultaneous_deresonance_badResidues

/-- The complement of the bad-residue union, i.e. residues where every minor de-resonates. -/
def conclusion_padic_hankel_simultaneous_deresonance_successResidues
    (D : conclusion_padic_hankel_simultaneous_deresonance_data) :
    Finset (Fin D.conclusion_padic_hankel_simultaneous_deresonance_q) :=
  Finset.univ \ D.conclusion_padic_hankel_simultaneous_deresonance_badResidueUnion

/-- The simultaneous valuation success predicate for one residue-field unit. -/
def conclusion_padic_hankel_simultaneous_deresonance_success
    (D : conclusion_padic_hankel_simultaneous_deresonance_data)
    (u : Fin D.conclusion_padic_hankel_simultaneous_deresonance_q) : Prop :=
  ∀ r,
    D.conclusion_padic_hankel_simultaneous_deresonance_valuation r u =
      D.conclusion_padic_hankel_simultaneous_deresonance_targetValuation r

/-- Finite counting form of the probability lower bound: the bad union has cardinality bounded by
the sum of the per-minor bad-residue bounds, and every residue outside that union satisfies all
valuation equalities. -/
def conclusion_padic_hankel_simultaneous_deresonance_success_probability_lower_bound
    (D : conclusion_padic_hankel_simultaneous_deresonance_data) : Prop :=
  D.conclusion_padic_hankel_simultaneous_deresonance_badResidueUnion.card ≤
      ∑ r : Fin D.conclusion_padic_hankel_simultaneous_deresonance_kappa,
        D.conclusion_padic_hankel_simultaneous_deresonance_perIndexBound r ∧
    ∀ u ∈ D.conclusion_padic_hankel_simultaneous_deresonance_successResidues,
      D.conclusion_padic_hankel_simultaneous_deresonance_success u

end conclusion_padic_hankel_simultaneous_deresonance_data

open conclusion_padic_hankel_simultaneous_deresonance_data

/-- Paper label: `thm:conclusion-padic-hankel-simultaneous-deresonance`. -/
theorem paper_conclusion_padic_hankel_simultaneous_deresonance
    (D : conclusion_padic_hankel_simultaneous_deresonance_data) :
    D.conclusion_padic_hankel_simultaneous_deresonance_success_probability_lower_bound := by
  classical
  constructor
  · calc
      D.conclusion_padic_hankel_simultaneous_deresonance_badResidueUnion.card
          ≤
            ∑ r ∈
                (Finset.univ :
                  Finset (Fin D.conclusion_padic_hankel_simultaneous_deresonance_kappa)),
              (D.conclusion_padic_hankel_simultaneous_deresonance_badResidues r).card := by
            unfold conclusion_padic_hankel_simultaneous_deresonance_badResidueUnion
            exact Finset.card_biUnion_le
      _ ≤
            ∑ r ∈
                (Finset.univ :
                  Finset (Fin D.conclusion_padic_hankel_simultaneous_deresonance_kappa)),
              D.conclusion_padic_hankel_simultaneous_deresonance_perIndexBound r := by
            exact Finset.sum_le_sum fun r _ =>
              D.conclusion_padic_hankel_simultaneous_deresonance_badResidues_card_bound r
      _ =
            ∑ r : Fin D.conclusion_padic_hankel_simultaneous_deresonance_kappa,
              D.conclusion_padic_hankel_simultaneous_deresonance_perIndexBound r := by
            simp
  · intro u hu
    exact
      D.conclusion_padic_hankel_simultaneous_deresonance_success_of_not_bad u
        (fun r hr =>
          (Finset.mem_sdiff.mp hu).2
            (by
              unfold conclusion_padic_hankel_simultaneous_deresonance_badResidueUnion
              exact Finset.mem_biUnion.mpr ⟨r, by simp, hr⟩))

end Omega.Conclusion
