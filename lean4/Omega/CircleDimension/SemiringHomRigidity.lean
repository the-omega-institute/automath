import Omega.Folding.CircleDimension

namespace Omega.CircleDimension

/-- Paper label: `thm:cdim-nr-nd-semiring-hom-rigidity`. -/
theorem paper_cdim_nr_nd_semiring_hom_rigidity
    (r d : ℕ) (f : (Fin r → ℕ) →+* (Fin d → ℕ)) :
    ∃ σ : Fin d → Fin r, ∀ x : Fin r → ℕ, ∀ j : Fin d, f x j = x (σ j) := by
  simpa using Omega.semiring_hom_rigidity r d f

/-- Paper label: `prop:cdim-nr-hom-idempotent-splitting`.
Homomorphisms from `ℕ^r` to a commutative semiring are equivalently complete orthogonal
idempotent splittings of `1`. -/
theorem paper_cdim_nr_hom_idempotent_splitting {S : Type*} [CommSemiring S] (r : ℕ) :
    Nonempty
      (((Fin r → ℕ) →+* S) ≃
        {ε : Fin r → S //
          (∀ i : Fin r, ε i * ε i = ε i) ∧
            (∀ i j : Fin r, i ≠ j → ε i * ε j = 0) ∧
            ∑ i : Fin r, ε i = 1}) := by
  classical
  refine ⟨
    { toFun := fun f =>
        ⟨fun i => f (Pi.single i 1), by
          refine ⟨?_, ?_, ?_⟩
          · intro i
            simpa [sq] using (Omega.semiring_hom_determines_idempotents r f i).1
          · intro i j hij
            exact (Omega.semiring_hom_determines_idempotents r f i).2.1 j hij
          · have hsum :
                (∑ i : Fin r, Pi.single i 1) = (1 : Fin r → ℕ) := by
              ext j
              simp [Finset.sum_apply, Pi.single_apply, Finset.mem_univ]
            calc
              ∑ i : Fin r, f (Pi.single i 1) = f (∑ i : Fin r, Pi.single i 1) := by
                rw [map_sum]
              _ = 1 := by rw [hsum, map_one]⟩
      invFun := fun E =>
        { toFun := fun x => ∑ i : Fin r, (x i : S) * E.1 i
          map_zero' := by simp
          map_one' := by simpa using E.2.2.2
          map_add' := by
            intro x y
            simp [add_mul, Finset.sum_add_distrib]
          map_mul' := by
            intro x y
            calc
              (∑ i : Fin r, ((x * y) i : S) * E.1 i)
                  = ∑ i : Fin r, ((x i : S) * (y i : S)) * E.1 i := by
                    simp [Pi.mul_apply]
              _ = (∑ i : Fin r, (x i : S) * E.1 i) *
                    (∑ j : Fin r, (y j : S) * E.1 j) := by
                    rw [Finset.sum_mul]
                    simp_rw [Finset.mul_sum]
                    refine (Finset.sum_congr rfl fun i _ => ?_).symm
                    calc
                      ∑ j : Fin r, ((x i : S) * E.1 i) * ((y j : S) * E.1 j)
                          = ((x i : S) * (y i : S)) * E.1 i := by
                            rw [Finset.sum_eq_single i]
                            · calc
                                ((x i : S) * E.1 i) * ((y i : S) * E.1 i)
                                    = ((x i : S) * (y i : S)) * (E.1 i * E.1 i) := by
                                      ring
                                _ = ((x i : S) * (y i : S)) * E.1 i := by
                                      rw [E.2.1 i]
                            · intro j _ hji
                              calc
                                ((x i : S) * E.1 i) * ((y j : S) * E.1 j)
                                    = ((x i : S) * (y j : S)) * (E.1 i * E.1 j) := by
                                      ring
                                _ = 0 := by rw [E.2.2.1 i j (Ne.symm hji), mul_zero]
                            · intro hi
                              exact False.elim (hi (Finset.mem_univ i))
                      _ = ((x i : S) * (y i : S)) * E.1 i := rfl }
      left_inv := by
        intro f
        apply DFunLike.ext
        intro x
        have hdecomp : x = ∑ i : Fin r, x i • Pi.single i 1 := by
          ext k
          simp [Finset.sum_apply, Pi.single_apply, Finset.mem_univ]
        calc
          (∑ i : Fin r, (x i : S) * f (Pi.single i 1))
              = ∑ i : Fin r, f (x i • Pi.single i 1) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            symm
            induction x i with
            | zero => simp
            | succ n ih =>
                simp [add_mul, map_add]
          _ = f (∑ i : Fin r, x i • Pi.single i 1) := by rw [map_sum]
          _ = f x := by rw [← hdecomp]
      right_inv := by
        intro E
        apply Subtype.ext
        funext i
        simp [Pi.single_apply] }⟩

end Omega.CircleDimension
