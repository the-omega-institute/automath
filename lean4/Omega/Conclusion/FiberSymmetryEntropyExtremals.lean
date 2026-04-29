import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- The product of factorial bucket sizes is bounded by the factorial of the total mass. -/
lemma conclusion_fiber_symmetry_entropy_extremals_factorial_prod_le_factorial_sum :
    ∀ multiplicity : List ℕ,
      (multiplicity.map Nat.factorial).prod ≤ Nat.factorial multiplicity.sum
  | [] => by simp
  | m :: multiplicity => by
      have htail :=
        conclusion_fiber_symmetry_entropy_extremals_factorial_prod_le_factorial_sum multiplicity
      calc
        ((m :: multiplicity).map Nat.factorial).prod =
            Nat.factorial m * (multiplicity.map Nat.factorial).prod := by
          simp
        _ ≤ Nat.factorial m * Nat.factorial multiplicity.sum := by
          exact Nat.mul_le_mul_left _ htail
        _ ≤ Nat.factorial (m + multiplicity.sum) := by
          exact Nat.le_of_dvd (Nat.factorial_pos _) <|
            Nat.factorial_mul_factorial_dvd_factorial_add m multiplicity.sum
        _ = Nat.factorial (m :: multiplicity).sum := by
          simp

/-- Each multiplicity bucket contributes at least one permutation. -/
lemma conclusion_fiber_symmetry_entropy_extremals_one_le_factorial_prod :
    ∀ multiplicity : List ℕ, 1 ≤ (multiplicity.map Nat.factorial).prod
  | [] => by simp
  | m :: multiplicity => by
      have htail :=
        conclusion_fiber_symmetry_entropy_extremals_one_le_factorial_prod multiplicity
      have hm : 1 ≤ Nat.factorial m := Nat.succ_le_of_lt (Nat.factorial_pos m)
      simpa using Nat.mul_le_mul hm htail

/-- List-form bucket factorial bounds used by the finite-bucket theorem below. -/
lemma conclusion_fiber_symmetry_entropy_extremals_list_bounds (multiplicity : List ℕ) :
    let r := multiplicity.sum
    1 ≤ (multiplicity.map Nat.factorial).prod ∧
      (multiplicity.map Nat.factorial).prod ≤ Nat.factorial r ∧
        2 ^ r ≤ 2 ^ r * (multiplicity.map Nat.factorial).prod ∧
          2 ^ r * (multiplicity.map Nat.factorial).prod ≤ 2 ^ r * Nat.factorial r := by
  dsimp
  constructor
  · exact conclusion_fiber_symmetry_entropy_extremals_one_le_factorial_prod multiplicity
  constructor
  · exact conclusion_fiber_symmetry_entropy_extremals_factorial_prod_le_factorial_sum multiplicity
  constructor
  · simpa using Nat.mul_le_mul_left (2 ^ multiplicity.sum) <|
      conclusion_fiber_symmetry_entropy_extremals_one_le_factorial_prod multiplicity
  · exact Nat.mul_le_mul_left (2 ^ multiplicity.sum) <|
      conclusion_fiber_symmetry_entropy_extremals_factorial_prod_le_factorial_sum multiplicity

/-- The bucket-factorial factor in the fiber automorphism count. -/
def conclusion_fiber_symmetry_entropy_extremals_bucketFactor {ι : Type} [Fintype ι]
    (m : ι → ℕ) : ℕ :=
  ∏ i, Nat.factorial (m i)

/-- The automorphism-cardinality model: independent flips and permutations inside equal buckets. -/
def conclusion_fiber_symmetry_entropy_extremals_autCard {ι : Type} [Fintype ι]
    (m : ι → ℕ) (r : ℕ) : ℕ :=
  2 ^ r * conclusion_fiber_symmetry_entropy_extremals_bucketFactor m

/-- Paper label: `thm:conclusion-fiber-symmetry-entropy-extremals`.
For a finite bucket profile with total mass `r`, the automorphism-cardinality factor is `2^r`
times the product of bucket factorials.  The factorial product lies between `1` and `r!`, with
the distinct-bucket and one-bucket configurations attaining the two endpoints. -/
theorem paper_conclusion_fiber_symmetry_entropy_extremals {ι : Type} [Fintype ι]
    [DecidableEq ι] (m : ι → ℕ) (r : ℕ) (hr : (Finset.univ.sum m) = r) :
    let bucketFactor := conclusion_fiber_symmetry_entropy_extremals_bucketFactor m
    let autCard := conclusion_fiber_symmetry_entropy_extremals_autCard m r
    autCard = 2 ^ r * bucketFactor ∧
      2 ^ r ≤ autCard ∧
      autCard ≤ 2 ^ r * Nat.factorial r ∧
      ((∀ i, m i ≤ 1) → autCard = 2 ^ r) ∧
      (∀ j, m j = r → (∀ i, i ≠ j → m i = 0) →
        autCard = 2 ^ r * Nat.factorial r) := by
  intro bucketFactor autCard
  have hfactor_pos : 0 < bucketFactor := by
    simpa [bucketFactor, conclusion_fiber_symmetry_entropy_extremals_bucketFactor] using
      (Finset.prod_pos (s := (Finset.univ : Finset ι))
        (f := fun i => Nat.factorial (m i)) (by intro i hi; exact Nat.factorial_pos _))
  have hfactor_lower : 1 ≤ bucketFactor := Nat.succ_le_of_lt hfactor_pos
  have hfactor_dvd :
      bucketFactor ∣ Nat.factorial r := by
    have h :=
      Nat.prod_factorial_dvd_factorial_sum (s := (Finset.univ : Finset ι)) (f := m)
    simpa [bucketFactor, conclusion_fiber_symmetry_entropy_extremals_bucketFactor, hr] using h
  have hfactor_upper : bucketFactor ≤ Nat.factorial r :=
    Nat.le_of_dvd (Nat.factorial_pos r) hfactor_dvd
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · calc
      2 ^ r = 2 ^ r * 1 := by rw [Nat.mul_one]
      _ ≤ autCard := by
        simpa [autCard, conclusion_fiber_symmetry_entropy_extremals_autCard] using
          Nat.mul_le_mul_left (2 ^ r) hfactor_lower
  · simpa [autCard, conclusion_fiber_symmetry_entropy_extremals_autCard] using
      Nat.mul_le_mul_left (2 ^ r) hfactor_upper
  · intro hdistinct
    have hbucket : conclusion_fiber_symmetry_entropy_extremals_bucketFactor m = 1 := by
      rw [conclusion_fiber_symmetry_entropy_extremals_bucketFactor]
      exact Finset.prod_eq_one (by
        intro i hi
        exact Nat.factorial_eq_one.mpr (hdistinct i))
    change conclusion_fiber_symmetry_entropy_extremals_autCard m r = 2 ^ r
    simp [conclusion_fiber_symmetry_entropy_extremals_autCard, hbucket]
  · intro j hj hzero
    have hbucket : conclusion_fiber_symmetry_entropy_extremals_bucketFactor m =
        Nat.factorial r := by
      rw [conclusion_fiber_symmetry_entropy_extremals_bucketFactor]
      calc
        (∏ i, Nat.factorial (m i)) = Nat.factorial (m j) := by
          exact Finset.prod_eq_single j (by
            intro i hi hij
            simp [hzero i hij]) (by simp)
        _ = Nat.factorial r := by rw [hj]
    change conclusion_fiber_symmetry_entropy_extremals_autCard m r =
      2 ^ r * Nat.factorial r
    simp [conclusion_fiber_symmetry_entropy_extremals_autCard, hbucket]

end Omega.Conclusion
