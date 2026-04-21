import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- The genus-`g` partition value written as a sum over fiber multiplicities. -/
def genusPartitionValue {n : ℕ} (multiplicity : Fin n → ℕ) (g : ℕ) : ℕ :=
  ∑ x, multiplicity x ^ g

@[simp] lemma genusPartitionValue_zero {n : ℕ} (multiplicity : Fin n → ℕ) :
    genusPartitionValue multiplicity 0 = n := by
  simp [genusPartitionValue]

lemma genusPartitionValue_all_one {n : ℕ} {multiplicity : Fin n → ℕ}
    (hall : ∀ x, multiplicity x = 1) :
    ∀ g, genusPartitionValue multiplicity g = n := by
  intro g
  simp [genusPartitionValue, hall]

lemma all_one_of_genus_zero_eq_genus_one {n : ℕ} {multiplicity : Fin n → ℕ}
    (hpos : ∀ x, 1 ≤ multiplicity x)
    (hEq : genusPartitionValue multiplicity 0 = genusPartitionValue multiplicity 1) :
    ∀ x, multiplicity x = 1 := by
  have hsum : ∑ x, multiplicity x = n := by
    calc
      ∑ x, multiplicity x = genusPartitionValue multiplicity 1 := by simp [genusPartitionValue]
      _ = genusPartitionValue multiplicity 0 := hEq.symm
      _ = n := genusPartitionValue_zero multiplicity
  have haux : ∑ x, (multiplicity x - 1) + n = ∑ x, multiplicity x := by
    calc
      ∑ x, (multiplicity x - 1) + n = ∑ x, (multiplicity x - 1) + ∑ x : Fin n, 1 := by simp
      _ = ∑ x, ((multiplicity x - 1) + 1) := by rw [← Finset.sum_add_distrib]
      _ = ∑ x, multiplicity x := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        exact Nat.sub_add_cancel (hpos x)
  have hzero : ∑ x, (multiplicity x - 1) = 0 := by
    have haux' : ∑ x, (multiplicity x - 1) + n = n := by simpa [hsum] using haux
    have haux'' : ∑ x, (multiplicity x - 1) + n = 0 + n := by simpa [zero_add] using haux'
    exact Nat.add_right_cancel haux''
  intro x
  have hx : multiplicity x - 1 = 0 := (Finset.sum_eq_zero_iff.mp hzero) x (by simp)
  have hm : multiplicity x = 0 + 1 := (tsub_eq_iff_eq_add_of_le (hpos x)).1 hx
  simpa using hm

lemma all_one_of_consecutive_genus_eq {n : ℕ} {multiplicity : Fin n → ℕ}
    (hpos : ∀ x, 1 ≤ multiplicity x) {g0 : ℕ}
    (hEq : genusPartitionValue multiplicity g0 = genusPartitionValue multiplicity (g0 + 1)) :
    ∀ x, multiplicity x = 1 := by
  have haux :
      ∑ x, (multiplicity x ^ g0 * (multiplicity x - 1)) + genusPartitionValue multiplicity g0 =
        genusPartitionValue multiplicity (g0 + 1) := by
    calc
      ∑ x, (multiplicity x ^ g0 * (multiplicity x - 1)) + genusPartitionValue multiplicity g0
          = ∑ x, (multiplicity x ^ g0 * (multiplicity x - 1)) + ∑ x, multiplicity x ^ g0 := by
              simp [genusPartitionValue]
      _ = ∑ x, (multiplicity x ^ g0 * (multiplicity x - 1) + multiplicity x ^ g0) := by
            rw [← Finset.sum_add_distrib]
      _ = ∑ x, multiplicity x ^ (g0 + 1) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            rw [pow_succ]
            calc
              multiplicity x ^ g0 * (multiplicity x - 1) + multiplicity x ^ g0
                  = multiplicity x ^ g0 * ((multiplicity x - 1) + 1) := by
                      rw [Nat.mul_add, Nat.mul_one]
              _ = multiplicity x ^ g0 * multiplicity x := by
                    rw [Nat.sub_add_cancel (hpos x)]
              _ = multiplicity x ^ (g0 + 1) := by rw [pow_succ]
  have hzero : ∑ x, multiplicity x ^ g0 * (multiplicity x - 1) = 0 := by
    have haux' :
        ∑ x, multiplicity x ^ g0 * (multiplicity x - 1) + genusPartitionValue multiplicity g0 =
          genusPartitionValue multiplicity g0 := by
      simpa [hEq] using haux
    have haux'' :
        ∑ x, multiplicity x ^ g0 * (multiplicity x - 1) + genusPartitionValue multiplicity g0 =
          0 + genusPartitionValue multiplicity g0 := by simpa [zero_add] using haux'
    exact Nat.add_right_cancel haux''
  intro x
  have hx : multiplicity x ^ g0 * (multiplicity x - 1) = 0 :=
    (Finset.sum_eq_zero_iff.mp hzero) x (by simp)
  have hsub : multiplicity x - 1 = 0 := by
    exact (Nat.mul_eq_zero.mp hx).resolve_left
      (pow_ne_zero _ (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 1) (hpos x))))
  have hm : multiplicity x = 0 + 1 := (tsub_eq_iff_eq_add_of_le (hpos x)).1 hsub
  simpa using hm

/-- The genus tower is trivial exactly when all fiber multiplicities are `1`; this is equivalent to
equality at genus `0` and `1`, to equality of one consecutive pair, and to constancy of the full
genus tower.
    thm:conclusion-tqft-genus-tower-trivialization-criterion -/
theorem paper_conclusion_tqft_genus_tower_trivialization_criterion
    {n : ℕ} (multiplicity : Fin n → ℕ) (hpos : ∀ x, 1 ≤ multiplicity x) :
    let Z := genusPartitionValue multiplicity
    ((∀ x, multiplicity x = 1) ↔ Z 0 = Z 1) ∧
      ((∀ x, multiplicity x = 1) ↔ Z 1 = Z 2) ∧
      ((∀ x, multiplicity x = 1) ↔ ∃ g0, Z g0 = Z (g0 + 1)) ∧
      ((∀ x, multiplicity x = 1) ↔ ∀ g, Z g = n) := by
  dsimp
  constructor
  · constructor
    · intro hall
      simpa using (genusPartitionValue_all_one hall 1).symm
    · intro hEq
      exact all_one_of_genus_zero_eq_genus_one hpos hEq
  constructor
  · constructor
    · intro hall
      have hAll := genusPartitionValue_all_one hall
      simp [hAll 1, hAll 2]
    · intro hEq
      exact all_one_of_consecutive_genus_eq hpos hEq
  constructor
  · constructor
    · intro hall
      exact ⟨0, by simpa using (genusPartitionValue_all_one hall 1).symm⟩
    · rintro ⟨g0, hg0⟩
      exact all_one_of_consecutive_genus_eq hpos hg0
  · constructor
    · intro hall
      exact genusPartitionValue_all_one hall
    · intro hall
      apply all_one_of_genus_zero_eq_genus_one hpos
      calc
        genusPartitionValue multiplicity 0 = n := genusPartitionValue_zero multiplicity
        _ = genusPartitionValue multiplicity 1 := (hall 1).symm

end Omega.Conclusion
