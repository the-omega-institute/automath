import Mathlib.Tactic
import Omega.Folding.FoldMultiplicityGroupAlgebra

open scoped BigOperators

namespace Omega.Folding

private def zeroIndex {m : ℕ} (hm : 0 < m) : Fin m := ⟨0, hm⟩

private def toggleZero {m : ℕ} (hm : 0 < m) (S : Finset (Fin m)) : Finset (Fin m) :=
  let z := zeroIndex hm
  if z ∈ S then S.erase z else insert z S

private def subsetSumEven (m : ℕ) (S : Finset (Fin m)) : Prop :=
  foldMultiplicitySubsetSum m S % 2 = 0

private def subsetSumOdd (m : ℕ) (S : Finset (Fin m)) : Prop :=
  foldMultiplicitySubsetSum m S % 2 = 1

private lemma foldMultiplicityGeneratorWeight_zero {m : ℕ} (hm : 0 < m) :
    foldMultiplicityGeneratorWeight m (zeroIndex hm) = 1 := by
  simp [zeroIndex, foldMultiplicityGeneratorWeight]

private lemma foldMultiplicitySubsetSum_insert_zero {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin m)) (hz : zeroIndex hm ∉ S) :
    foldMultiplicitySubsetSum m (insert (zeroIndex hm) S) = foldMultiplicitySubsetSum m S + 1 := by
  rw [foldMultiplicitySubsetSum, Finset.sum_insert hz, foldMultiplicitySubsetSum,
    foldMultiplicityGeneratorWeight_zero hm]
  omega

private lemma foldMultiplicitySubsetSum_eq_erase_add_one {m : ℕ} (hm : 0 < m)
    (S : Finset (Fin m)) (hz : zeroIndex hm ∈ S) :
    foldMultiplicitySubsetSum m S = foldMultiplicitySubsetSum m (S.erase (zeroIndex hm)) + 1 := by
  simpa [Finset.insert_erase hz] using
    (foldMultiplicitySubsetSum_insert_zero hm (S.erase (zeroIndex hm)) (by simp))

private lemma toggleZero_involutive {m : ℕ} (hm : 0 < m) :
    Function.Involutive (toggleZero hm) := by
  intro S
  unfold toggleZero
  by_cases hz : zeroIndex hm ∈ S
  · simp [hz]
  · simp [hz]

private lemma toggleZero_subsetSum_mod_two {m : ℕ} (hm : 0 < m) (S : Finset (Fin m)) :
    foldMultiplicitySubsetSum m (toggleZero hm S) % 2 =
      if foldMultiplicitySubsetSum m S % 2 = 0 then 1 else 0 := by
  by_cases hz : zeroIndex hm ∈ S
  · have hsum :
        foldMultiplicitySubsetSum m S =
          foldMultiplicitySubsetSum m (S.erase (zeroIndex hm)) + 1 :=
      foldMultiplicitySubsetSum_eq_erase_add_one hm S hz
    unfold toggleZero
    simp [hz]
    rcases Nat.mod_two_eq_zero_or_one (foldMultiplicitySubsetSum m S) with hpar | hpar
    · simp [hpar]
      omega
    · simp [hpar]
      omega
  · have hsum :
        foldMultiplicitySubsetSum m (insert (zeroIndex hm) S) =
          foldMultiplicitySubsetSum m S + 1 :=
      foldMultiplicitySubsetSum_insert_zero hm S hz
    unfold toggleZero
    rw [if_neg hz, hsum, Nat.add_mod]
    rcases Nat.mod_two_eq_zero_or_one (foldMultiplicitySubsetSum m S) with hpar | hpar
    · simp [hpar]
    · simp [hpar]

/-- Paper label: `cor:fold-even-odd-balance`. -/
theorem paper_fold_even_odd_balance (m : ℕ)
    (hEven : Even (Omega.Folding.foldMultiplicityModulus m)) :
    let evenTotal := ∑ r : Fin (Omega.Folding.foldMultiplicityModulus m),
      if r.1 % 2 = 0 then Omega.Folding.foldMultiplicityGeneratingPolynomial m r else 0
    let oddTotal := ∑ r : Fin (Omega.Folding.foldMultiplicityModulus m),
      if r.1 % 2 = 1 then Omega.Folding.foldMultiplicityGeneratingPolynomial m r else 0
    evenTotal = 2 ^ (m - 1) ∧ oddTotal = 2 ^ (m - 1) := by
  classical
  have hmpos : 0 < m := by
    cases m with
    | zero =>
        simp [foldMultiplicityModulus] at hEven
    | succ n =>
        exact Nat.succ_pos _
  let family : Finset (Finset (Fin m)) := foldMultiplicitySubsetFamily m
  let evenSubsets : Finset (Finset (Fin m)) := family.filter (subsetSumEven m)
  let oddSubsets : Finset (Finset (Fin m)) := family.filter (subsetSumOdd m)
  have hmodEven : foldMultiplicityModulus m % 2 = 0 := by
    rcases hEven with ⟨k, hk⟩
    omega
  have hResidueParity :
      ∀ S : Finset (Fin m),
        (foldMultiplicityResidue m S).1 % 2 = foldMultiplicitySubsetSum m S % 2 := by
    intro S
    simpa [foldMultiplicityResidue] using
      (Nat.mod_mod_of_dvd (foldMultiplicitySubsetSum m S) hEven.two_dvd)
  have hevenTotal :
      (∑ r : Fin (foldMultiplicityModulus m),
        if r.1 % 2 = 0 then foldMultiplicityGeneratingPolynomial m r else 0) =
        evenSubsets.card := by
    calc
      (∑ r : Fin (foldMultiplicityModulus m),
        if r.1 % 2 = 0 then foldMultiplicityGeneratingPolynomial m r else 0)
          =
            ∑ r : Fin (foldMultiplicityModulus m),
              if r.1 % 2 = 0 then foldMultiplicitySubsetProductCoeff m r else 0 := by
                refine Finset.sum_congr rfl ?_
                intro r hr
                by_cases hpar : r.1 % 2 = 0
                · simp [hpar, paper_fold_multiplicity_group_algebra m r]
                · simp [hpar]
      _ =
          ∑ r : Fin (foldMultiplicityModulus m),
            if r.1 % 2 = 0 then
              Finset.sum family (fun S => if foldMultiplicityResidue m S = r then 1 else 0)
            else 0 := by
            simp [family, foldMultiplicitySubsetProductCoeff]
      _ =
          ∑ r : Fin (foldMultiplicityModulus m),
            Finset.sum family (fun S =>
              if r.1 % 2 = 0 then if foldMultiplicityResidue m S = r then 1 else 0 else 0) := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            by_cases hpar : r.1 % 2 = 0
            · simp [hpar]
            · simp [hpar]
      _ =
          Finset.sum family fun S =>
            ∑ r : Fin (foldMultiplicityModulus m),
              if r.1 % 2 = 0 then if foldMultiplicityResidue m S = r then 1 else 0 else 0 := by
            rw [Finset.sum_comm]
      _ =
          Finset.sum family fun S =>
            if (foldMultiplicityResidue m S).1 % 2 = 0 then 1 else 0 := by
            refine Finset.sum_congr rfl ?_
            intro S hS
            rw [Finset.sum_eq_single (foldMultiplicityResidue m S)]
            · by_cases hpar : (foldMultiplicityResidue m S).1 % 2 = 0
              · simp [hpar]
              · simp [hpar]
            · intro r _ hr
              by_cases hpar : r.1 % 2 = 0
              · have hneq : foldMultiplicityResidue m S ≠ r := by
                  intro h
                  exact hr h.symm
                simp [hpar, hneq]
              · simp [hpar]
            · intro hr
              simp at hr
      _ =
          Finset.sum family fun S =>
            if foldMultiplicitySubsetSum m S % 2 = 0 then 1 else 0 := by
            refine Finset.sum_congr rfl ?_
            intro S hS
            rw [← hResidueParity S]
      _ = evenSubsets.card := by
            show (Finset.sum family fun S => if foldMultiplicitySubsetSum m S % 2 = 0 then 1 else 0) =
              (family.filter (subsetSumEven m)).card
            rw [← Finset.sum_filter]
            simp
            have hfilter :
                {a ∈ family | foldMultiplicitySubsetSum m a % 2 = 0} = family.filter (subsetSumEven m) := by
              ext a
              simp [subsetSumEven]
            simp [hfilter]
  have hoddTotal :
      (∑ r : Fin (foldMultiplicityModulus m),
        if r.1 % 2 = 1 then foldMultiplicityGeneratingPolynomial m r else 0) =
        oddSubsets.card := by
    calc
      (∑ r : Fin (foldMultiplicityModulus m),
        if r.1 % 2 = 1 then foldMultiplicityGeneratingPolynomial m r else 0)
          =
            ∑ r : Fin (foldMultiplicityModulus m),
              if r.1 % 2 = 1 then foldMultiplicitySubsetProductCoeff m r else 0 := by
                refine Finset.sum_congr rfl ?_
                intro r hr
                by_cases hpar : r.1 % 2 = 1
                · simp [hpar, paper_fold_multiplicity_group_algebra m r]
                · simp [hpar]
      _ =
          ∑ r : Fin (foldMultiplicityModulus m),
            if r.1 % 2 = 1 then
              Finset.sum family (fun S => if foldMultiplicityResidue m S = r then 1 else 0)
            else 0 := by
            simp [family, foldMultiplicitySubsetProductCoeff]
      _ =
          ∑ r : Fin (foldMultiplicityModulus m),
            Finset.sum family (fun S =>
              if r.1 % 2 = 1 then if foldMultiplicityResidue m S = r then 1 else 0 else 0) := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            by_cases hpar : r.1 % 2 = 1
            · simp [hpar]
            · simp [hpar]
      _ =
          Finset.sum family fun S =>
            ∑ r : Fin (foldMultiplicityModulus m),
              if r.1 % 2 = 1 then if foldMultiplicityResidue m S = r then 1 else 0 else 0 := by
            rw [Finset.sum_comm]
      _ =
          Finset.sum family fun S =>
            if (foldMultiplicityResidue m S).1 % 2 = 1 then 1 else 0 := by
            refine Finset.sum_congr rfl ?_
            intro S hS
            rw [Finset.sum_eq_single (foldMultiplicityResidue m S)]
            · by_cases hpar : (foldMultiplicityResidue m S).1 % 2 = 1
              · simp [hpar]
              · simp [hpar]
            · intro r _ hr
              by_cases hpar : r.1 % 2 = 1
              · have hneq : foldMultiplicityResidue m S ≠ r := by
                  intro h
                  exact hr h.symm
                simp [hpar, hneq]
              · simp [hpar]
            · intro hr
              simp at hr
      _ =
          Finset.sum family fun S =>
            if foldMultiplicitySubsetSum m S % 2 = 1 then 1 else 0 := by
            refine Finset.sum_congr rfl ?_
            intro S hS
            rw [← hResidueParity S]
      _ = oddSubsets.card := by
            show (Finset.sum family fun S => if foldMultiplicitySubsetSum m S % 2 = 1 then 1 else 0) =
              (family.filter (subsetSumOdd m)).card
            rw [← Finset.sum_filter]
            simp
            have hfilter :
                {a ∈ family | foldMultiplicitySubsetSum m a % 2 = 1} = family.filter (subsetSumOdd m) := by
              ext a
              simp [subsetSumOdd]
            simp [hfilter]
  have htoggle_mem :
      ∀ S : Finset (Fin m), S ∈ evenSubsets ↔ toggleZero hmpos S ∈ oddSubsets := by
    intro S
    simp [evenSubsets, oddSubsets, family, foldMultiplicitySubsetFamily, subsetSumEven,
      subsetSumOdd, toggleZero_subsetSum_mod_two]
  have hcard_eq : evenSubsets.card = oddSubsets.card := by
    exact Finset.card_bijective (toggleZero hmpos) (toggleZero_involutive hmpos).bijective htoggle_mem
  have hodd_not :
      family.filter (fun S => ¬ subsetSumEven m S) = oddSubsets := by
    ext S
    rcases Nat.mod_two_eq_zero_or_one (foldMultiplicitySubsetSum m S) with hpar | hpar
    · simp [oddSubsets, subsetSumEven, subsetSumOdd, hpar]
    · simp [oddSubsets, subsetSumEven, subsetSumOdd, hpar]
  have hpartition :
      evenSubsets.card + oddSubsets.card = family.card := by
    rw [← Finset.card_filter_add_card_filter_not (s := family) (p := subsetSumEven m), hodd_not]
  have hfamily_card : family.card = 2 ^ m := by
    simp [family, foldMultiplicitySubsetFamily]
  have hdouble : evenSubsets.card + evenSubsets.card = 2 ^ m := by
    calc
      evenSubsets.card + evenSubsets.card = evenSubsets.card + oddSubsets.card := by
        rw [hcard_eq]
      _ = family.card := hpartition
      _ = 2 ^ m := hfamily_card
  have heven_card : evenSubsets.card = 2 ^ (m - 1) := by
    cases m with
    | zero =>
        cases (Nat.not_lt_zero 0 hmpos)
    | succ n =>
        have hsucc : evenSubsets.card + evenSubsets.card = 2 * 2 ^ n := by
          simpa [Nat.pow_succ, Nat.mul_comm] using hdouble
        have hcard : evenSubsets.card = 2 ^ n := by
          omega
        simpa using hcard
  have hodd_card : oddSubsets.card = 2 ^ (m - 1) := by
    rw [← hcard_eq]
    exact heven_card
  dsimp
  exact ⟨hevenTotal.trans heven_card, hoddTotal.trans hodd_card⟩

end Omega.Folding
