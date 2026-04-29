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

private lemma conclusion_fold_normalized_walsh_weighted_simplex_geometry_sum_fibers
    (m : ℕ) (f : Word m → ℝ) :
    ∑ x : X m, ∑ w ∈ X.fiber x, f w = ∑ w : Word m, f w := by
  classical
  have hDisjoint : (↑(Finset.univ : Finset (X m)) : Set (X m)).PairwiseDisjoint X.fiber := by
    intro x _ y _ hxy
    rw [Function.onFun, Finset.disjoint_left]
    intro w hwx hwy
    exact hxy ((X.mem_fiber.1 hwx).symm.trans (X.mem_fiber.1 hwy))
  have hUnion : (Finset.univ : Finset (Word m)) = Finset.univ.biUnion X.fiber := by
    ext w
    simp only [Finset.mem_univ, Finset.mem_biUnion, true_iff]
    exact ⟨Fold w, trivial, X.mem_fiber_Fold w⟩
  calc
    ∑ x : X m, ∑ w ∈ X.fiber x, f w
        = ∑ w ∈ Finset.univ.biUnion X.fiber, f w := by
            simpa using (Finset.sum_biUnion hDisjoint (f := f)).symm
    _ = ∑ w : Word m, f w := by rw [← hUnion]

private lemma conclusion_fold_normalized_walsh_weighted_simplex_geometry_walsh_total_zero
    {m : ℕ} {I : Finset (Fin m)} (hI : I ∈ nonemptySubsets m) :
    ∑ w : Word m, walshCharacter m w I = 0 := by
  classical
  have hne : I ≠ ∅ := by
    exact (Finset.mem_erase.mp (by simpa [nonemptySubsets] using hI)).1
  obtain ⟨i, hiI⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  let τ : Word m ≃ Word m := {
    toFun := fun w j => if j = i then !w j else w j
    invFun := fun w j => if j = i then !w j else w j
    left_inv w := by
      funext j
      by_cases hji : j = i
      · simp [hji]
      · simp [hji]
    right_inv w := by
      funext j
      by_cases hji : j = i
      · simp [hji]
      · simp [hji] }
  have htoggle : ∀ w : Word m, walshCharacter m (τ w) I = -walshCharacter m w I := by
    intro w
    have hi_toggle : coordSign (τ w) i = -coordSign w i := by
      by_cases hwi : w i <;> simp [τ, coordSign, hwi]
    have hsame : ∀ j ∈ I.erase i, coordSign (τ w) j = coordSign w j := by
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      simp [τ, coordSign, hji]
    calc
      walshCharacter m (τ w) I
          = coordSign (τ w) i * ∏ j ∈ I.erase i, coordSign (τ w) j := by
              rw [walshCharacter, Finset.mul_prod_erase I (fun j => coordSign (τ w) j) hiI]
      _ = (-coordSign w i) * ∏ j ∈ I.erase i, coordSign w j := by
              rw [hi_toggle]
              congr 1
              apply Finset.prod_congr rfl
              exact hsame
      _ = -(coordSign w i * ∏ j ∈ I.erase i, coordSign w j) := by ring
      _ = -walshCharacter m w I := by
              rw [walshCharacter, Finset.mul_prod_erase I (fun j => coordSign w j) hiI]
  have hsum_perm :
      ∑ w : Word m, walshCharacter m (τ w) I = ∑ w : Word m, walshCharacter m w I :=
    Equiv.sum_comp τ (fun w => walshCharacter m w I)
  have hneg :
      ∑ w : Word m, walshCharacter m (τ w) I = -∑ w : Word m, walshCharacter m w I := by
    simp [htoggle]
  linarith

private lemma conclusion_fold_normalized_walsh_weighted_simplex_geometry_profile_total_zero
    {m : ℕ} {I : Finset (Fin m)} (hI : I ∈ nonemptySubsets m) :
    ∑ x : X m, walshProfile m x I = 0 := by
  classical
  calc
    ∑ x : X m, walshProfile m x I
        = ∑ x : X m, ∑ w ∈ X.fiber x, walshCharacter m w I := by
            simp [walshProfile]
    _ = ∑ w : Word m, walshCharacter m w I :=
            conclusion_fold_normalized_walsh_weighted_simplex_geometry_sum_fibers
              (m := m) (f := fun w => walshCharacter m w I)
    _ = 0 := conclusion_fold_normalized_walsh_weighted_simplex_geometry_walsh_total_zero hI

/-- thm:conclusion-fold-normalized-walsh-weighted-simplex-geometry -/
theorem paper_conclusion_fold_normalized_walsh_weighted_simplex_geometry (m : ℕ) :
    (∀ x y : X m, x ≠ y →
      ∑ I ∈ nonemptySubsets m,
        (walshProfile m x I / (X.fiberMultiplicity x : ℝ)) *
          (walshProfile m y I / (X.fiberMultiplicity y : ℝ)) = -1) ∧
    (∀ x : X m,
      ∑ I ∈ nonemptySubsets m, (walshProfile m x I / (X.fiberMultiplicity x : ℝ)) ^ 2 =
        (2 : ℝ) ^ m / (X.fiberMultiplicity x : ℝ) - 1) ∧
    (∀ x y : X m, x ≠ y →
      ∑ I ∈ nonemptySubsets m,
        ((walshProfile m x I / (X.fiberMultiplicity x : ℝ)) -
          (walshProfile m y I / (X.fiberMultiplicity y : ℝ))) ^ 2 =
        (2 : ℝ) ^ m *
          (1 / (X.fiberMultiplicity x : ℝ) + 1 / (X.fiberMultiplicity y : ℝ))) ∧
    (∀ I, I ∈ nonemptySubsets m →
      ∑ x : X m,
        ((X.fiberMultiplicity x : ℝ) / (2 : ℝ) ^ m) *
          (walshProfile m x I / (X.fiberMultiplicity x : ℝ)) = 0) := by
  classical
  have hpow_ne : (2 : ℝ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hxy
    have hx : (X.fiberMultiplicity x : ℝ) ≠ 0 := by
      exact_mod_cast ne_of_gt (X.fiberMultiplicity_pos x)
    have hy : (X.fiberMultiplicity y : ℝ) ≠ 0 := by
      exact_mod_cast ne_of_gt (X.fiberMultiplicity_pos y)
    have hgram := paper_conclusion_fold_nontrivial_walsh_exact_gram_law m x y
    calc
      ∑ I ∈ nonemptySubsets m,
          (walshProfile m x I / (X.fiberMultiplicity x : ℝ)) *
            (walshProfile m y I / (X.fiberMultiplicity y : ℝ))
          = (∑ I ∈ nonemptySubsets m, walshProfile m x I * walshProfile m y I) /
              ((X.fiberMultiplicity x : ℝ) * (X.fiberMultiplicity y : ℝ)) := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro I hI
              field_simp [hx, hy]
      _ = -1 := by
              rw [hgram]
              simp [hxy]
              field_simp [hx, hy]
  · intro x
    have hx : (X.fiberMultiplicity x : ℝ) ≠ 0 := by
      exact_mod_cast ne_of_gt (X.fiberMultiplicity_pos x)
    have hgram := paper_conclusion_fold_nontrivial_walsh_exact_gram_law m x x
    calc
      ∑ I ∈ nonemptySubsets m, (walshProfile m x I / (X.fiberMultiplicity x : ℝ)) ^ 2
          = (∑ I ∈ nonemptySubsets m, walshProfile m x I * walshProfile m x I) /
              ((X.fiberMultiplicity x : ℝ) ^ 2) := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro I hI
              field_simp [hx]
      _ = (2 : ℝ) ^ m / (X.fiberMultiplicity x : ℝ) - 1 := by
              rw [hgram]
              simp
              field_simp [hx]
  · intro x y hxy
    have hx : (X.fiberMultiplicity x : ℝ) ≠ 0 := by
      exact_mod_cast ne_of_gt (X.fiberMultiplicity_pos x)
    have hy : (X.fiberMultiplicity y : ℝ) ≠ 0 := by
      exact_mod_cast ne_of_gt (X.fiberMultiplicity_pos y)
    have hxyInner :
        ∑ I ∈ nonemptySubsets m,
          (walshProfile m x I / (X.fiberMultiplicity x : ℝ)) *
            (walshProfile m y I / (X.fiberMultiplicity y : ℝ)) = -1 := by
      have hgram := paper_conclusion_fold_nontrivial_walsh_exact_gram_law m x y
      calc
        ∑ I ∈ nonemptySubsets m,
            (walshProfile m x I / (X.fiberMultiplicity x : ℝ)) *
              (walshProfile m y I / (X.fiberMultiplicity y : ℝ))
            = (∑ I ∈ nonemptySubsets m, walshProfile m x I * walshProfile m y I) /
                ((X.fiberMultiplicity x : ℝ) * (X.fiberMultiplicity y : ℝ)) := by
                rw [Finset.sum_div]
                apply Finset.sum_congr rfl
                intro I hI
                field_simp [hx, hy]
        _ = -1 := by
                rw [hgram]
                simp [hxy]
                field_simp [hx, hy]
    have hxNorm :
        ∑ I ∈ nonemptySubsets m, (walshProfile m x I / (X.fiberMultiplicity x : ℝ)) ^ 2 =
          (2 : ℝ) ^ m / (X.fiberMultiplicity x : ℝ) - 1 := by
      have hgram := paper_conclusion_fold_nontrivial_walsh_exact_gram_law m x x
      calc
        ∑ I ∈ nonemptySubsets m, (walshProfile m x I / (X.fiberMultiplicity x : ℝ)) ^ 2
            = (∑ I ∈ nonemptySubsets m, walshProfile m x I * walshProfile m x I) /
                ((X.fiberMultiplicity x : ℝ) ^ 2) := by
                rw [Finset.sum_div]
                apply Finset.sum_congr rfl
                intro I hI
                field_simp [hx]
        _ = (2 : ℝ) ^ m / (X.fiberMultiplicity x : ℝ) - 1 := by
                rw [hgram]
                simp
                field_simp [hx]
    have hyNorm :
        ∑ I ∈ nonemptySubsets m, (walshProfile m y I / (X.fiberMultiplicity y : ℝ)) ^ 2 =
          (2 : ℝ) ^ m / (X.fiberMultiplicity y : ℝ) - 1 := by
      have hgram := paper_conclusion_fold_nontrivial_walsh_exact_gram_law m y y
      calc
        ∑ I ∈ nonemptySubsets m, (walshProfile m y I / (X.fiberMultiplicity y : ℝ)) ^ 2
            = (∑ I ∈ nonemptySubsets m, walshProfile m y I * walshProfile m y I) /
                ((X.fiberMultiplicity y : ℝ) ^ 2) := by
                rw [Finset.sum_div]
                apply Finset.sum_congr rfl
                intro I hI
                field_simp [hy]
        _ = (2 : ℝ) ^ m / (X.fiberMultiplicity y : ℝ) - 1 := by
                rw [hgram]
                simp
                field_simp [hy]
    calc
      ∑ I ∈ nonemptySubsets m,
          ((walshProfile m x I / (X.fiberMultiplicity x : ℝ)) -
            (walshProfile m y I / (X.fiberMultiplicity y : ℝ))) ^ 2
          =
          ∑ I ∈ nonemptySubsets m,
            ((walshProfile m x I / (X.fiberMultiplicity x : ℝ)) ^ 2 +
              (walshProfile m y I / (X.fiberMultiplicity y : ℝ)) ^ 2 -
              2 * ((walshProfile m x I / (X.fiberMultiplicity x : ℝ)) *
                (walshProfile m y I / (X.fiberMultiplicity y : ℝ)))) := by
              apply Finset.sum_congr rfl
              intro I hI
              ring
      _ =
          ∑ I ∈ nonemptySubsets m, (walshProfile m x I / (X.fiberMultiplicity x : ℝ)) ^ 2 +
            ∑ I ∈ nonemptySubsets m, (walshProfile m y I / (X.fiberMultiplicity y : ℝ)) ^ 2 -
            2 * ∑ I ∈ nonemptySubsets m,
              (walshProfile m x I / (X.fiberMultiplicity x : ℝ)) *
                (walshProfile m y I / (X.fiberMultiplicity y : ℝ)) := by
              rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
              simp [Finset.mul_sum]
      _ = (2 : ℝ) ^ m *
          (1 / (X.fiberMultiplicity x : ℝ) + 1 / (X.fiberMultiplicity y : ℝ)) := by
              rw [hxyInner, hxNorm, hyNorm]
              field_simp [hx, hy]
              ring
  · intro I hI
    have htotal := conclusion_fold_normalized_walsh_weighted_simplex_geometry_profile_total_zero
      (m := m) hI
    calc
      ∑ x : X m,
          ((X.fiberMultiplicity x : ℝ) / (2 : ℝ) ^ m) *
            (walshProfile m x I / (X.fiberMultiplicity x : ℝ))
          = ∑ x : X m, walshProfile m x I / (2 : ℝ) ^ m := by
              apply Finset.sum_congr rfl
              intro x hxmem
              have hx : (X.fiberMultiplicity x : ℝ) ≠ 0 := by
                exact_mod_cast ne_of_gt (X.fiberMultiplicity_pos x)
              field_simp [hx, hpow_ne]
      _ = 0 := by
              rw [← Finset.sum_div, htotal]
              simp

end

end Omega.Conclusion
