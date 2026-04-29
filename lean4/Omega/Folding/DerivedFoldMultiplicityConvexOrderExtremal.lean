import Mathlib.Tactic

namespace Omega.Folding

open scoped BigOperators

/-- A balanced nat-valued profile whose values are all `a` or `a + 1` is determined by the
Euclidean division data `M = aF + ρ`; the number of `a + 1` entries is `ρ`, the number of `a`
entries is `F - ρ`, and its quadratic moment is the corresponding extremal value.
    thm:derived-fold-multiplicity-convex-order-extremal -/
theorem paper_derived_fold_multiplicity_convex_order_extremal
    {F M : ℕ} (hF : 0 < F) (d : Fin F → ℕ)
    (hvals : ∀ i, d i = M / F ∨ d i = M / F + 1) (hsum : ∑ i, d i = M) :
    let a := M / F
    let ρ := M % F
    ((Finset.univ.filter fun i => d i = a + 1).card = ρ) ∧
      ((Finset.univ.filter fun i => d i = a).card = F - ρ) ∧
      (∑ i, d i ^ 2 = (F - ρ) * a ^ 2 + ρ * (a + 1) ^ 2) := by
  classical
  let a := M / F
  let ρ := M % F
  let A : Finset (Fin F) := Finset.univ.filter fun i => d i = a
  let S : Finset (Fin F) := Finset.univ.filter fun i => d i = a + 1
  have hMdecomp : M = F * a + ρ := by
    simpa [a, ρ, Nat.add_comm, Nat.mul_comm] using (Nat.mod_add_div M F).symm
  have hcardS_from_sum : M = F * a + S.card := by
    calc
      M = ∑ i : Fin F, d i := hsum.symm
      _ = ∑ i : Fin F, (a + if i ∈ S then 1 else 0) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        by_cases hiS : i ∈ S
        · have hd : d i = a + 1 := by
            simpa [S] using (Finset.mem_filter.mp hiS).2
          simp [hiS, hd]
        · have hval : d i = a ∨ d i = a + 1 := by
            simpa [a] using hvals i
          rcases hval with hd | hd
          · simp [hiS, hd]
          · exfalso
            exact hiS (by simpa [S, hd])
      _ = (∑ i : Fin F, a) + ∑ i : Fin F, if i ∈ S then 1 else 0 := by
        rw [Finset.sum_add_distrib]
      _ = F * a + S.card := by
        simp [S]
  have hcardS : S.card = ρ := by
    omega
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
  have hcardA : A.card = F - ρ := by
    have hpart :
        S.card + (Finset.univ.filter fun i : Fin F => ¬ d i = a + 1).card = F := by
      simpa using
        (Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin F))) (p := fun i : Fin F => d i = a + 1))
    rw [hA_notS] at hpart
    omega
  have hsqA : A.sum (fun i => d i ^ 2) = A.card * a ^ 2 := by
    calc
      A.sum (fun i => d i ^ 2) = A.sum (fun _ => a ^ 2) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hd : d i = a := by
          simpa [A] using (Finset.mem_filter.mp hi).2
        simp [hd]
      _ = A.card * a ^ 2 := by simp
  have hsqS : S.sum (fun i => d i ^ 2) = S.card * (a + 1) ^ 2 := by
    calc
      S.sum (fun i => d i ^ 2) = S.sum (fun _ => (a + 1) ^ 2) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hd : d i = a + 1 := by
          simpa [S] using (Finset.mem_filter.mp hi).2
        simp [hd]
      _ = S.card * (a + 1) ^ 2 := by simp
  have hsq :
      ∑ i : Fin F, d i ^ 2 = (F - ρ) * a ^ 2 + ρ * (a + 1) ^ 2 := by
    calc
      ∑ i : Fin F, d i ^ 2 =
          S.sum (fun i => d i ^ 2) +
            (Finset.univ.filter fun i : Fin F => ¬ d i = a + 1).sum (fun i => d i ^ 2) := by
              symm
              simpa [S] using
                (Finset.sum_filter_add_sum_filter_not
                  (s := (Finset.univ : Finset (Fin F))) (p := fun i : Fin F => d i = a + 1)
                  (f := fun i : Fin F => d i ^ 2))
      _ = S.sum (fun i => d i ^ 2) + A.sum (fun i => d i ^ 2) := by rw [hA_notS]
      _ = S.card * (a + 1) ^ 2 + A.card * a ^ 2 := by rw [hsqS, hsqA]
      _ = (F - ρ) * a ^ 2 + ρ * (a + 1) ^ 2 := by
            rw [hcardS, hcardA]
            ac_rfl
  simpa [a, ρ] using ⟨hcardS, hcardA, hsq⟩

end Omega.Folding
