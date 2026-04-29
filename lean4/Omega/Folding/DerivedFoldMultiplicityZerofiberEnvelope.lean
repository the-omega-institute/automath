import Mathlib.Tactic
import Omega.Folding.DerivedFoldMultiplicityConvexOrderExtremal

namespace Omega.Folding

open scoped BigOperators

private theorem balanced_profile_capacity
    {n M : ℕ} (d : Fin n → ℕ)
    (hvals : ∀ i, d i = M / n ∨ d i = M / n + 1) (T : ℕ) :
    ∑ i, Nat.min (d i) T =
      (Finset.univ.filter fun i => d i = M / n).card * Nat.min (M / n) T +
        (Finset.univ.filter fun i => d i = M / n + 1).card * Nat.min (M / n + 1) T := by
  let a := M / n
  let A : Finset (Fin n) := Finset.univ.filter fun i => d i = a
  let S : Finset (Fin n) := Finset.univ.filter fun i => d i = a + 1
  have hA_notS : (Finset.univ.filter fun i : Fin n => ¬ d i = a + 1) = A := by
    ext i
    constructor
    · intro hi
      have hval : d i = a ∨ d i = a + 1 := by
        simpa [a] using hvals i
      have hnot : ¬ d i = a + 1 := (Finset.mem_filter.mp hi).2
      rcases hval with hd | hd
      · simp [A, hd]
      · exact False.elim (hnot hd)
    · intro hi
      have hd : d i = a := by
        simpa [A] using (Finset.mem_filter.mp hi).2
      simp [hd]
  calc
    ∑ i : Fin n, Nat.min (d i) T =
        S.sum (fun i => Nat.min (d i) T) +
          (Finset.univ.filter fun i : Fin n => ¬ d i = a + 1).sum (fun i => Nat.min (d i) T) := by
            symm
            simpa [S] using
              (Finset.sum_filter_add_sum_filter_not
                (s := (Finset.univ : Finset (Fin n))) (p := fun i : Fin n => d i = a + 1)
                (f := fun i : Fin n => Nat.min (d i) T))
    _ = S.sum (fun i => Nat.min (d i) T) + A.sum (fun i => Nat.min (d i) T) := by rw [hA_notS]
    _ = S.card * Nat.min (a + 1) T + A.card * Nat.min a T := by
          congr 1
          · calc
              S.sum (fun i => Nat.min (d i) T) = S.sum (fun _ => Nat.min (a + 1) T) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                have hd : d i = a + 1 := by
                  simpa [S] using (Finset.mem_filter.mp hi).2
                simp [hd]
              _ = S.card * Nat.min (a + 1) T := by simp
          · calc
              A.sum (fun i => Nat.min (d i) T) = A.sum (fun _ => Nat.min a T) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                have hd : d i = a := by
                  simpa [A] using (Finset.mem_filter.mp hi).2
                simp [hd]
              _ = A.card * Nat.min a T := by simp
    _ = A.card * Nat.min a T + S.card * Nat.min (a + 1) T := by ac_rfl
    _ = (Finset.univ.filter fun i => d i = a).card * Nat.min a T +
          (Finset.univ.filter fun i => d i = a + 1).card * Nat.min (a + 1) T := by
            rfl

/-- Paper label: `thm:derived-fold-multiplicity-zerofiber-envelope`.
The `z` zero fibers are kept implicit by working on the nonzero support of size `F - z`. The
balanced two-level profile on that support simultaneously realizes the quadratic moment, the
derived nonzero Fourier energy, the truncated capacity curve, and the top-fiber value. -/
theorem paper_derived_fold_multiplicity_zerofiber_envelope
    {F M z : ℕ} (hF : 0 < F) (hz : z < F) (d : Fin (F - z) → ℕ)
    (hvals : ∀ i, d i = M / (F - z) ∨ d i = M / (F - z) + 1)
    (hsum : ∑ i, d i = M) :
    let n := F - z
    let a := M / n
    let ρ := M % n
    (∑ i, d i ^ 2 = (n - ρ) * a ^ 2 + ρ * (a + 1) ^ 2) ∧
      (F * (∑ i, d i ^ 2) - M ^ 2 = F * ((n - ρ) * a ^ 2 + ρ * (a + 1) ^ 2) - M ^ 2) ∧
      (∀ T : ℕ, ∑ i, Nat.min (d i) T = (n - ρ) * Nat.min a T + ρ * Nat.min (a + 1) T) ∧
      (∃ i, d i = a + if ρ = 0 then 0 else 1) := by
  let _ := hF
  let a := M / (F - z)
  let ρ := M % (F - z)
  have hn : 0 < F - z := by omega
  have hExt :=
    paper_derived_fold_multiplicity_convex_order_extremal (F := F - z) (M := M) hn d hvals hsum
  rcases (by simpa [a, ρ] using hExt) with ⟨hcardS, hcardA, hsq⟩
  have hcap :
      ∀ T : ℕ,
        ∑ i, Nat.min (d i) T = (F - z - ρ) * Nat.min a T + ρ * Nat.min (a + 1) T := by
    intro T
    have hcap' := balanced_profile_capacity d hvals T
    simpa [a, ρ, hcardA, hcardS] using hcap'
  have htop : ∃ i, d i = a + if ρ = 0 then 0 else 1 := by
    by_cases hρ : ρ = 0
    · have hcardS0 : (Finset.univ.filter fun i : Fin (F - z) => d i = a + 1).card = 0 := by
        rw [hcardS]
        simpa [ρ] using hρ
      have hSempty : Finset.univ.filter (fun i : Fin (F - z) => d i = a + 1) = ∅ :=
        Finset.card_eq_zero.mp hcardS0
      have hAllA : ∀ i, d i = a := by
        intro i
        have hval : d i = a ∨ d i = a + 1 := by
          simpa [a] using hvals i
        rcases hval with hd | hd
        · exact hd
        · exfalso
          have hi : i ∈ Finset.univ.filter (fun j : Fin (F - z) => d j = a + 1) := by simp [hd]
          simpa [hSempty] using hi
      refine ⟨⟨0, hn⟩, ?_⟩
      simpa [hρ] using hAllA ⟨0, hn⟩
    · have hρpos : 0 < ρ := Nat.pos_of_ne_zero hρ
      have hcardSpos : 0 < (Finset.univ.filter fun i : Fin (F - z) => d i = a + 1).card := by
        rw [hcardS]
        exact hρpos
      rcases Finset.card_pos.mp hcardSpos with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      have hd : d i = a + 1 := by
        simpa using (Finset.mem_filter.mp hi).2
      simpa [hρ] using hd
  simpa [a, ρ] using ⟨hsq, by rw [hsq], hcap, htop⟩

end Omega.Folding
