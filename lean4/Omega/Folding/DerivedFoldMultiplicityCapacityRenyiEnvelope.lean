import Mathlib.Tactic
import Omega.Folding.DerivedFoldMultiplicityConvexOrderExtremal

namespace Omega.Folding

open scoped BigOperators

private theorem balanced_profile_capacity
    {F M : ℕ} (d : Fin F → ℕ)
    (hvals : ∀ i, d i = M / F ∨ d i = M / F + 1) (T : ℕ) :
    ∑ i, min (d i) T =
      (Finset.univ.filter fun i => d i = M / F).card * min (M / F) T +
        (Finset.univ.filter fun i => d i = M / F + 1).card * min (M / F + 1) T := by
  let a := M / F
  let A : Finset (Fin F) := Finset.univ.filter fun i => d i = a
  let S : Finset (Fin F) := Finset.univ.filter fun i => d i = a + 1
  have hA_notS : (Finset.univ.filter fun i : Fin F => ¬ d i = a + 1) = A := by
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
    ∑ i : Fin F, min (d i) T =
        S.sum (fun i => min (d i) T) +
          (Finset.univ.filter fun i : Fin F => ¬ d i = a + 1).sum (fun i => min (d i) T) := by
            symm
            simpa [S] using
              (Finset.sum_filter_add_sum_filter_not
                (s := (Finset.univ : Finset (Fin F))) (p := fun i : Fin F => d i = a + 1)
                (f := fun i : Fin F => min (d i) T))
    _ = S.sum (fun i => min (d i) T) + A.sum (fun i => min (d i) T) := by rw [hA_notS]
    _ = S.card * min (a + 1) T + A.card * min a T := by
          congr 1
          · calc
              S.sum (fun i => min (d i) T) = S.sum (fun _ => min (a + 1) T) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                have hd : d i = a + 1 := by
                  simpa [S] using (Finset.mem_filter.mp hi).2
                simp [hd]
              _ = S.card * min (a + 1) T := by simp
          · calc
              A.sum (fun i => min (d i) T) = A.sum (fun _ => min a T) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                have hd : d i = a := by
                  simpa [A] using (Finset.mem_filter.mp hi).2
                simp [hd]
              _ = A.card * min a T := by simp
    _ = A.card * min a T + S.card * min (a + 1) T := by ac_rfl
    _ = (Finset.univ.filter fun i => d i = a).card * min a T +
          (Finset.univ.filter fun i => d i = a + 1).card * min (a + 1) T := by
            rfl

/-- Paper label: `thm:derived-fold-multiplicity-capacity-renyi-envelope`.
For a balanced multiplicity profile taking only the values `a` and `a + 1`, the truncated
capacity sum is exactly the two-level envelope determined by the Euclidean division data. -/
theorem paper_derived_fold_multiplicity_capacity_renyi_envelope {F M T : ℕ} (hF : 0 < F)
    (d : Fin F → ℕ) (hvals : ∀ i, d i = M / F ∨ d i = M / F + 1) (hsum : ∑ i, d i = M) :
    ∑ i, min (d i) T ≤
      (F - M % F) * min (M / F) T + (M % F) * min (M / F + 1) T := by
  have hExt :=
    paper_derived_fold_multiplicity_convex_order_extremal (F := F) (M := M) hF d hvals hsum
  rcases (by simpa using hExt) with ⟨hcardS, hcardA, _hsq⟩
  have hcap := balanced_profile_capacity d hvals T
  simpa [hcardA, hcardS] using le_of_eq hcap

end Omega.Folding
