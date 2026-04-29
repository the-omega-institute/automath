import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Folding.ModSemiringsAnnihilatorValuationLattice

namespace Omega

/-- The squarefree radical of the fold semiring modulus `F_{m+2}`. -/
def foldModSemiringRadical (m : ℕ) : ℕ :=
  (foldModSemiringModulus m).primeFactors.prod id

private lemma foldModSemiringRadical_dvd_modulus (m : ℕ) :
    foldModSemiringRadical m ∣ foldModSemiringModulus m := by
  simpa [foldModSemiringRadical] using Nat.prod_primeFactors_dvd (foldModSemiringModulus m)

private lemma foldModSemiringRadical_pos (m : ℕ) :
    0 < foldModSemiringRadical m := by
  unfold foldModSemiringRadical
  exact Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos

private lemma foldModSemiringRadical_squarefree (m : ℕ) :
    Squarefree (foldModSemiringRadical m) := by
  unfold foldModSemiringRadical
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · intro p hp q hq hpq
    exact (Nat.coprime_iff_isRelPrime).1 <|
      (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp) (Nat.prime_of_mem_primeFactors hq)).2 hpq
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).squarefree

private lemma card_range_filter_dvd (n r : ℕ) (hdiv : r ∣ n) :
    ((Finset.range n).filter (fun a => r ∣ a)).card = n / r := by
  rcases hdiv with ⟨q, rfl⟩
  by_cases hr : r = 0
  · subst hr
    simp
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    calc
      ((Finset.range (r * q)).filter (fun a => r ∣ a)).card = (Finset.range q).card := by
        refine (Finset.card_bij (s := Finset.range q)
          (t := (Finset.range (r * q)).filter (fun a => r ∣ a)) (i := fun k _ => r * k)
          ?_ ?_ ?_).symm
        · intro k hk
          rw [Finset.mem_filter]
          refine ⟨by
            rw [Finset.mem_range]
            exact Nat.mul_lt_mul_of_pos_left (Finset.mem_range.mp hk) hrpos,
            dvd_mul_of_dvd_left (dvd_refl r) k⟩
        · intro a ha b hb hab
          exact mul_left_cancel₀ hr hab
        · intro a ha
          simp only [Finset.mem_filter, Finset.mem_range] at ha
          refine ⟨a / r, ?_, ?_⟩
          · by_contra h
            have hq : ¬a / r < q := by simpa [Finset.mem_range] using h
            have hq' : q ≤ a / r := Nat.not_lt.mp hq
            have hm : r * q ≤ r * (a / r) := Nat.mul_le_mul_left r hq'
            have : r * q ≤ a := by simpa [Nat.mul_div_cancel' ha.2] using hm
            exact (Nat.not_le_of_gt ha.1) this
          · simp [Nat.mul_div_cancel' ha.2]
      _ = q := by simp
      _ = (r * q) / r := by
        symm
        exact Nat.mul_div_right q hrpos

/-- In `ZMod (F_{m+2})`, the nilpotent branch is exactly the radical-divisible residue-class layer,
and it is trivial precisely in the squarefree case.
    thm:fold-mod-semirings-squarefree-nilpotent-branch -/
theorem paper_fold_mod_semirings_squarefree_nilpotent_branch (m : ℕ) :
    let n := Omega.foldModSemiringModulus m
    let r := foldModSemiringRadical m
    ((Finset.range n).filter (fun a => r ∣ a)).card = n / r ∧
      (Squarefree n ↔ ((Finset.range n).filter (fun a => a ≠ 0 ∧ r ∣ a)).card = 0) := by
  dsimp
  let n := foldModSemiringModulus m
  let r := foldModSemiringRadical m
  have hn_pos : 0 < n := by
    dsimp [n, foldModSemiringModulus]
    exact Nat.fib_pos.2 (by omega)
  have hr_dvd_n : r ∣ n := by
    dsimp [r, n]
    exact foldModSemiringRadical_dvd_modulus m
  have hr_pos : 0 < r := by
    dsimp [r]
    exact foldModSemiringRadical_pos m
  refine ⟨by simpa [n, r] using card_range_filter_dvd n r hr_dvd_n, ?_⟩
  constructor
  · intro hn_sq
    by_contra hne
    rcases Finset.card_pos.mp (Nat.pos_of_ne_zero hne) with ⟨a, ha⟩
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    have hr_eq_n : r = n := by
      dsimp [r, n, foldModSemiringRadical]
      exact Nat.prod_primeFactors_of_squarefree hn_sq
    have hna : n ∣ a := by
      rw [← hr_eq_n]
      exact ha.2.2
    have hle : n ≤ a := Nat.le_of_dvd (Nat.pos_of_ne_zero ha.2.1) hna
    exact (Nat.not_lt.mpr hle) ha.1
  · intro hcard
    by_contra hn_sq
    have hr_sq : Squarefree r := by
      dsimp [r]
      exact foldModSemiringRadical_squarefree m
    have hr_ne_n : r ≠ n := by
      intro h
      exact hn_sq (by simpa [h] using hr_sq)
    have hr_lt_n : r < n := lt_of_le_of_ne (Nat.le_of_dvd hn_pos hr_dvd_n) hr_ne_n
    have hr_mem : r ∈ (Finset.range n).filter (fun a => a ≠ 0 ∧ r ∣ a) := by
      simp [hr_lt_n, hr_pos.ne']
    exact (Finset.card_pos.mpr ⟨r, hr_mem⟩).ne' hcard

end Omega
