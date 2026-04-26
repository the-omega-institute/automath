import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Omega.Folding.Fiber

open scoped BigOperators

namespace Omega.Conclusion

noncomputable section

local instance (m : ℕ) : DecidableEq (Word m) :=
  Classical.decEq _

local instance (m : ℕ) : DecidableEq (X m) :=
  Classical.decEq _

/-- All subsets of the coordinate index set. -/
def allSubsets (m : ℕ) : Finset (Finset (Fin m)) :=
  (Finset.univ : Finset (Fin m)).powerset

/-- The nonempty Walsh modes. -/
def nonemptySubsets (m : ℕ) : Finset (Finset (Fin m)) :=
  (allSubsets m).erase ∅

/-- The `{-1,1}` sign attached to a single coordinate. -/
def coordSign {m : ℕ} (w : Word m) (i : Fin m) : ℝ :=
  if w i then (-1 : ℝ) else 1

/-- The Walsh character indexed by `I`. -/
def walshCharacter (m : ℕ) (w : Word m) (I : Finset (Fin m)) : ℝ :=
  ∏ i ∈ I, coordSign w i

/-- Fiberwise Walsh coefficient for a stable output `x`. -/
def walshProfile (m : ℕ) (x : X m) (I : Finset (Fin m)) : ℝ :=
  ∑ w ∈ X.fiber x, walshCharacter m w I

@[simp] lemma walshCharacter_empty (m : ℕ) (w : Word m) :
    walshCharacter m w ∅ = 1 := by
  simp [walshCharacter]

@[simp] lemma walshProfile_empty (m : ℕ) (x : X m) :
    walshProfile m x ∅ = X.fiberMultiplicity x := by
  simp [walshProfile, walshCharacter, X.fiberMultiplicity]

lemma sum_allSubsets_walshCharacter (m : ℕ) (u v : Word m) :
    ∑ I ∈ allSubsets m, walshCharacter m u I * walshCharacter m v I =
      if u = v then (2 : ℝ) ^ m else 0 := by
  classical
  by_cases huv : u = v
  · subst huv
    have hrewrite :
        (∑ I ∈ allSubsets m, walshCharacter m u I * walshCharacter m u I) =
          ∑ I ∈ allSubsets m, ∏ i ∈ I, coordSign u i * coordSign u i := by
      apply Finset.sum_congr rfl
      intro I hI
      simp [walshCharacter, Finset.prod_mul_distrib]
    rw [hrewrite]
    rw [allSubsets,
      ← Finset.prod_one_add (s := (Finset.univ : Finset (Fin m)))
        (f := fun i => coordSign u i * coordSign u i)]
    have hprod :
        (∏ i ∈ (Finset.univ : Finset (Fin m)), (1 + coordSign u i * coordSign u i)) =
          ∏ i ∈ (Finset.univ : Finset (Fin m)), (2 : ℝ) := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases h : u i
      · simp [coordSign, h]
        norm_num
      · simp [coordSign, h]
        norm_num
    rw [hprod]
    simp
  · have hrewrite :
        (∑ I ∈ allSubsets m, walshCharacter m u I * walshCharacter m v I) =
          ∑ I ∈ allSubsets m, ∏ i ∈ I, coordSign u i * coordSign v i := by
      apply Finset.sum_congr rfl
      intro I hI
      simp [walshCharacter, Finset.prod_mul_distrib]
    rw [hrewrite]
    rw [allSubsets,
      ← Finset.prod_one_add (s := (Finset.univ : Finset (Fin m)))
        (f := fun i => coordSign u i * coordSign v i)]
    have hnot : ¬ ∀ i : Fin m, u i = v i := by
      intro hall
      apply huv
      funext i
      exact hall i
    rcases Classical.not_forall.mp hnot with ⟨i, hi⟩
    have hzero : 1 + coordSign u i * coordSign v i = 0 := by
      by_cases hu : u i <;> by_cases hv : v i <;> simp [coordSign, hu, hv] at hi ⊢
    rw [if_neg huv]
    exact Finset.prod_eq_zero_iff.mpr ⟨i, by simp, hzero⟩

lemma fiberDiagonalSum (m : ℕ) (x y : X m) :
    ∑ w ∈ X.fiber x, ∑ v ∈ X.fiber y, (if w = v then (2 : ℝ) ^ m else 0) =
      (2 : ℝ) ^ m * (X.fiberMultiplicity x : ℝ) * (if x = y then 1 else 0) := by
  classical
  by_cases hxy : x = y
  · subst hxy
    calc
      ∑ w ∈ X.fiber x, ∑ v ∈ X.fiber x, (if w = v then (2 : ℝ) ^ m else 0)
          = ∑ w ∈ X.fiber x, (2 : ℝ) ^ m := by
              apply Finset.sum_congr rfl
              intro w hw
              rw [Finset.sum_eq_single_of_mem w hw]
              · simp
              · intro v hv hvw
                by_cases h : w = v
                · exact False.elim (hvw h.symm)
                · simp [h]
      _ = ((X.fiber x).card : ℝ) * (2 : ℝ) ^ m := by
            simp
      _ = (2 : ℝ) ^ m * (X.fiberMultiplicity x : ℝ) * (if x = x then 1 else 0) := by
            simp [X.fiberMultiplicity, mul_comm, mul_left_comm, mul_assoc]
  · calc
      ∑ w ∈ X.fiber x, ∑ v ∈ X.fiber y, (if w = v then (2 : ℝ) ^ m else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro w hw
        apply Finset.sum_eq_zero
        intro v hv
        have hne : w ≠ v := by
          intro hwv
          apply hxy
          calc
            x = Fold w := ((X.mem_fiber).1 hw).symm
            _ = Fold v := by simpa [hwv]
            _ = y := (X.mem_fiber).1 hv
        simp [hne]
      _ = (2 : ℝ) ^ m * (X.fiberMultiplicity x : ℝ) * (if x = y then 1 else 0) := by
            simp [hxy]

/-- The nontrivial Walsh modes satisfy the exact Gram law obtained by removing the empty
character contribution from the full Parseval identity.
    thm:conclusion-fold-nontrivial-walsh-exact-gram-law -/
theorem paper_conclusion_fold_nontrivial_walsh_exact_gram_law (m : ℕ) (x y : X m) :
    ∑ I ∈ nonemptySubsets m, walshProfile m x I * walshProfile m y I =
      (2 : ℝ) ^ m * (X.fiberMultiplicity x : ℝ) * (if x = y then 1 else 0) -
        (X.fiberMultiplicity x : ℝ) * (X.fiberMultiplicity y : ℝ) := by
  classical
  let F : Finset (Fin m) → ℝ := fun I => walshProfile m x I * walshProfile m y I
  have hsplit :
      ∑ I ∈ allSubsets m, F I = ∑ I ∈ nonemptySubsets m, F I + F ∅ := by
    simpa [allSubsets, nonemptySubsets, add_comm] using
      (Finset.sum_erase_add (s := allSubsets m) (f := F) (a := ∅) (by simp))
  have hfull :
      ∑ I ∈ allSubsets m, F I =
        (2 : ℝ) ^ m * (X.fiberMultiplicity x : ℝ) * (if x = y then 1 else 0) := by
    unfold F
    simp_rw [walshProfile, Finset.sum_mul, Finset.mul_sum]
    calc
      ∑ I ∈ allSubsets m, ∑ w ∈ X.fiber x, ∑ v ∈ X.fiber y,
          walshCharacter m w I * walshCharacter m v I
          = ∑ w ∈ X.fiber x, ∑ I ∈ allSubsets m, ∑ v ∈ X.fiber y,
              walshCharacter m w I * walshCharacter m v I := by
              rw [Finset.sum_comm]
      _ = ∑ w ∈ X.fiber x, ∑ v ∈ X.fiber y, ∑ I ∈ allSubsets m,
            walshCharacter m w I * walshCharacter m v I := by
            apply Finset.sum_congr rfl
            intro w hw
            rw [Finset.sum_comm]
      _ = ∑ w ∈ X.fiber x, ∑ v ∈ X.fiber y, (if w = v then (2 : ℝ) ^ m else 0) := by
            apply Finset.sum_congr rfl
            intro w hw
            apply Finset.sum_congr rfl
            intro v hv
            rw [sum_allSubsets_walshCharacter]
      _ = (2 : ℝ) ^ m * (X.fiberMultiplicity x : ℝ) * (if x = y then 1 else 0) :=
            fiberDiagonalSum m x y
  have hempty : F ∅ = (X.fiberMultiplicity x : ℝ) * (X.fiberMultiplicity y : ℝ) := by
    simp [F, walshProfile_empty]
  change ∑ I ∈ nonemptySubsets m, F I =
    (2 : ℝ) ^ m * (X.fiberMultiplicity x : ℝ) * (if x = y then 1 else 0) -
      (X.fiberMultiplicity x : ℝ) * (X.fiberMultiplicity y : ℝ)
  linarith [hsplit, hfull, hempty]

/-- Boundary-visible Walsh energy is exact, and some nonempty Walsh mode carries at least the
average visible energy.
    cor:conclusion-fold-boundary-visible-energy-nonremovable-mode -/
theorem paper_conclusion_fold_boundary_visible_energy_nonremovable_mode (m : ℕ) (hm : 1 ≤ m)
    (x : X m) :
    (∑ I ∈ nonemptySubsets m, walshProfile m x I ^ 2 =
      (X.fiberMultiplicity x : ℝ) *
        ((2 : ℝ) ^ m - (X.fiberMultiplicity x : ℝ))) ∧
    (∃ I, I ∈ nonemptySubsets m ∧
      ((X.fiberMultiplicity x : ℝ) *
          ((2 : ℝ) ^ m - (X.fiberMultiplicity x : ℝ))) / ((2 : ℝ) ^ m - 1) ≤
        walshProfile m x I ^ 2) := by
  classical
  let energy : ℝ :=
    (X.fiberMultiplicity x : ℝ) * ((2 : ℝ) ^ m - (X.fiberMultiplicity x : ℝ))
  have henergy :
      ∑ I ∈ nonemptySubsets m, walshProfile m x I ^ 2 = energy := by
    calc
      ∑ I ∈ nonemptySubsets m, walshProfile m x I ^ 2
          = ∑ I ∈ nonemptySubsets m, walshProfile m x I * walshProfile m x I := by
              simp [pow_two]
      _ = (2 : ℝ) ^ m * (X.fiberMultiplicity x : ℝ) * (if x = x then 1 else 0) -
          (X.fiberMultiplicity x : ℝ) * (X.fiberMultiplicity x : ℝ) :=
            paper_conclusion_fold_nontrivial_walsh_exact_gram_law m x x
      _ = energy := by
            simp [energy]
            ring
  refine ⟨by simpa [energy] using henergy, ?_⟩
  let S : Finset (Finset (Fin m)) := nonemptySubsets m
  let f : Finset (Fin m) → ℝ := fun I => walshProfile m x I ^ 2
  have hmpos : 0 < m := Nat.lt_of_lt_of_le Nat.zero_lt_one hm
  let i : Fin m := ⟨0, hmpos⟩
  have hS : S.Nonempty := by
    refine ⟨{i}, ?_⟩
    simp [S, nonemptySubsets, allSubsets]
  obtain ⟨I, hI, hmax⟩ := Finset.exists_max_image S f hS
  refine ⟨I, by simpa [S] using hI, ?_⟩
  have hsum_le : ∑ J ∈ S, f J ≤ S.card • f I := by
    simpa using S.sum_le_card_nsmul f (f I) hmax
  have hsum_eq : ∑ J ∈ S, f J = energy := by
    simpa [S, f] using henergy
  have henergy_le : energy ≤ (S.card : ℝ) * f I := by
    calc
      energy = ∑ J ∈ S, f J := hsum_eq.symm
      _ ≤ S.card • f I := hsum_le
      _ = (S.card : ℝ) * f I := by simp [nsmul_eq_mul]
  have hcard_nat : S.card = 2 ^ m - 1 := by
    simp [S, nonemptySubsets, allSubsets]
  have hpow_ge_one : 1 ≤ 2 ^ m := by
    exact Nat.one_le_pow m 2 (by norm_num)
  have hcard_real : (S.card : ℝ) = (2 : ℝ) ^ m - 1 := by
    rw [hcard_nat, Nat.cast_sub hpow_ge_one]
    norm_num
  have hcard_pos : 0 < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hS
  have haverage_le : energy / (S.card : ℝ) ≤ f I := by
    rw [div_le_iff₀ hcard_pos]
    simpa [mul_comm] using henergy_le
  simpa [energy, S, f, hcard_real] using haverage_le

end

end Omega.Conclusion
