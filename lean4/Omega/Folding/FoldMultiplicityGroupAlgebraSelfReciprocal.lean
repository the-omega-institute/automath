import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic
import Omega.Core.Fib
import Omega.Folding.FoldMultiplicityGroupAlgebra

namespace Omega.Folding

private def foldMultiplicityComplementIndex (m r : ℕ) : ℕ :=
  (Nat.fib (m + 1) - 2 + (foldMultiplicityModulus m - r)) % foldMultiplicityModulus m

private lemma foldMultiplicityFibLowerBound (m : ℕ) (hm : 2 ≤ m) : 2 ≤ Nat.fib (m + 1) := by
  calc
    Nat.fib (m + 1) ≥ Nat.fib 3 := Nat.fib_mono (by omega)
    _ = 2 := by native_decide

private lemma foldMultiplicityShift_lt_modulus (m : ℕ) (hm : 2 ≤ m) :
    Nat.fib (m + 1) - 2 < foldMultiplicityModulus m := by
  have hF1_ge2 : 2 ≤ Nat.fib (m + 1) := foldMultiplicityFibLowerBound m hm
  have hmono : Nat.fib (m + 1) ≤ Nat.fib (m + 2) := Nat.fib_mono (by omega)
  simp [foldMultiplicityModulus]
  omega

private lemma foldMultiplicitySubsetSum_univ (m : ℕ) :
    foldMultiplicitySubsetSum m (Finset.univ : Finset (Fin m)) = Nat.fib (m + 3) - 2 := by
  unfold foldMultiplicitySubsetSum foldMultiplicityGeneratorWeight
  calc
    (∑ x : Fin m, Nat.fib (↑x + 2)) = ∑ i ∈ Finset.range m, Nat.fib (i + 2) := by
      simpa using (Fin.sum_univ_eq_sum_range (n := m) (f := fun i : ℕ => Nat.fib (i + 2)))
    _ = Nat.fib (m + 3) - 2 := Omega.fib_weight_sum_range m

private lemma foldMultiplicitySubsetSum_complement_add (m : ℕ) (S : Finset (Fin m)) :
    foldMultiplicitySubsetSum m ((Finset.univ : Finset (Fin m)) \ S) +
        foldMultiplicitySubsetSum m S =
      Nat.fib (m + 3) - 2 := by
  have hsubset : S ⊆ (Finset.univ : Finset (Fin m)) := Finset.subset_univ S
  have hsum :
      Finset.sum ((Finset.univ : Finset (Fin m)) \ S) (fun j => foldMultiplicityGeneratorWeight m j) +
          Finset.sum S (fun j => foldMultiplicityGeneratorWeight m j) =
        Finset.sum Finset.univ (fun j : Fin m => foldMultiplicityGeneratorWeight m j) := by
    simpa using (Finset.sum_sdiff hsubset (f := fun j : Fin m => foldMultiplicityGeneratorWeight m j))
  calc
    foldMultiplicitySubsetSum m ((Finset.univ : Finset (Fin m)) \ S) +
        foldMultiplicitySubsetSum m S
        = Finset.sum Finset.univ (fun j : Fin m => foldMultiplicityGeneratorWeight m j) := by
            simpa [foldMultiplicitySubsetSum] using hsum
    _ = Nat.fib (m + 3) - 2 := by
          exact foldMultiplicitySubsetSum_univ m

private lemma foldMultiplicityComplementIndex_involutive (m : ℕ) (hm : 2 ≤ m)
    (r : ℕ) (hr : r < foldMultiplicityModulus m) :
    foldMultiplicityComplementIndex m (foldMultiplicityComplementIndex m r) = r := by
  have hc_lt : Nat.fib (m + 1) - 2 < foldMultiplicityModulus m := foldMultiplicityShift_lt_modulus m hm
  by_cases hrc : r ≤ Nat.fib (m + 1) - 2
  · have hfirst :
        foldMultiplicityComplementIndex m r =
          Nat.fib (m + 1) - 2 - r := by
        have hdecomp :
            Nat.fib (m + 1) - 2 + (foldMultiplicityModulus m - r) =
              foldMultiplicityModulus m + (Nat.fib (m + 1) - 2 - r) := by
          omega
        unfold foldMultiplicityComplementIndex
        rw [hdecomp, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]
        exact Nat.mod_eq_of_lt (by
          have hlt : Nat.fib (m + 1) - 2 - r < foldMultiplicityModulus m := by
            omega
          exact hlt)
    rw [hfirst]
    unfold foldMultiplicityComplementIndex
    have hdecomp :
        Nat.fib (m + 1) - 2 + (foldMultiplicityModulus m - (Nat.fib (m + 1) - 2 - r)) =
          foldMultiplicityModulus m + r := by
      omega
    rw [hdecomp, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hr]
  · have hrc' : Nat.fib (m + 1) - 2 < r := by omega
    have hfirst :
        foldMultiplicityComplementIndex m r =
          Nat.fib (m + 1) - 2 + (foldMultiplicityModulus m - r) := by
      unfold foldMultiplicityComplementIndex
      exact Nat.mod_eq_of_lt (by
        have hlt : Nat.fib (m + 1) - 2 + (foldMultiplicityModulus m - r) <
            foldMultiplicityModulus m := by
          omega
        exact hlt)
    rw [hfirst]
    unfold foldMultiplicityComplementIndex
    have hdecomp :
        Nat.fib (m + 1) - 2 +
            (foldMultiplicityModulus m -
              (Nat.fib (m + 1) - 2 + (foldMultiplicityModulus m - r))) =
          r := by
      omega
    rw [hdecomp, Nat.mod_eq_of_lt hr]

private lemma foldMultiplicityResidue_complement (m : ℕ) (hm : 2 ≤ m)
    (S : Finset (Fin m)) (r : Fin (foldMultiplicityModulus m))
    (hres : foldMultiplicityResidue m S = r) :
    foldMultiplicityResidue m ((Finset.univ : Finset (Fin m)) \ S) =
      ⟨foldMultiplicityComplementIndex m r.1,
        Nat.mod_lt _ (foldMultiplicityModulus_pos m)⟩ := by
  apply Fin.ext
  have hsum :
      foldMultiplicitySubsetSum m ((Finset.univ : Finset (Fin m)) \ S) +
          foldMultiplicitySubsetSum m S =
        Nat.fib (m + 3) - 2 := foldMultiplicitySubsetSum_complement_add m S
  have hsum' :
      foldMultiplicitySubsetSum m ((Finset.univ : Finset (Fin m)) \ S) +
          foldMultiplicitySubsetSum m S =
        Nat.fib (m + 1) - 2 + foldMultiplicityModulus m := by
    have hF1_ge2 : 2 ≤ Nat.fib (m + 1) := foldMultiplicityFibLowerBound m hm
    have hFib3 : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using (Nat.fib_add_two (n := m + 1))
    calc
      foldMultiplicitySubsetSum m ((Finset.univ : Finset (Fin m)) \ S) +
          foldMultiplicitySubsetSum m S =
        Nat.fib (m + 3) - 2 := hsum
      _ = Nat.fib (m + 1) - 2 + foldMultiplicityModulus m := by
            rw [foldMultiplicityModulus, hFib3]
            omega
  have hmodS : foldMultiplicitySubsetSum m S % foldMultiplicityModulus m = r.1 := by
    simpa [foldMultiplicityResidue] using congrArg Fin.val hres
  have hSmodEq :
      foldMultiplicitySubsetSum m S ≡ r.1 [MOD foldMultiplicityModulus m] := by
    simpa [Nat.ModEq, Nat.mod_eq_of_lt r.2] using hmodS
  have hsumEq :
      foldMultiplicitySubsetSum m ((Finset.univ : Finset (Fin m)) \ S) +
          foldMultiplicitySubsetSum m S ≡
        (Nat.fib (m + 1) - 2 + (foldMultiplicityModulus m - r.1)) + r.1
          [MOD foldMultiplicityModulus m] := by
    rw [Nat.ModEq]
    calc
      (foldMultiplicitySubsetSum m ((Finset.univ : Finset (Fin m)) \ S) +
          foldMultiplicitySubsetSum m S) %
          foldMultiplicityModulus m
          = (Nat.fib (m + 1) - 2 + foldMultiplicityModulus m) % foldMultiplicityModulus m := by
              rw [hsum']
      _ = ((Nat.fib (m + 1) - 2 + (foldMultiplicityModulus m - r.1)) + r.1) %
            foldMultiplicityModulus m := by
              congr 1
              omega
  have hcomp :
      foldMultiplicitySubsetSum m ((Finset.univ : Finset (Fin m)) \ S) ≡
        Nat.fib (m + 1) - 2 + (foldMultiplicityModulus m - r.1)
          [MOD foldMultiplicityModulus m] := by
    exact Nat.ModEq.add_right_cancel hSmodEq hsumEq
  simpa [foldMultiplicityResidue, foldMultiplicityComplementIndex, Nat.ModEq] using hcomp

/-- Paper label: `cor:fold-multiplicity-group-algebra-self-reciprocal`.
Complementing a subset flips the residue class by the affine shift `F_{m+1}-2`, and this
involution preserves the coefficient count in the group-algebra multiplicity profile. -/
theorem paper_fold_multiplicity_group_algebra_self_reciprocal (m : ℕ) (hm : 2 ≤ m) (r : ℕ)
    (hr : r < Omega.Folding.foldMultiplicityModulus m) :
    Omega.Folding.foldMultiplicityGeneratingPolynomial m ⟨r, hr⟩ =
      Omega.Folding.foldMultiplicityGeneratingPolynomial m
        ⟨(Nat.fib (m + 1) - 2 + (Omega.Folding.foldMultiplicityModulus m - r)) %
            Omega.Folding.foldMultiplicityModulus m,
          by exact Nat.mod_lt _ (Omega.Folding.foldMultiplicityModulus_pos m)⟩ := by
  classical
  let source :=
    ((foldMultiplicitySubsetFamily m).filter fun S => foldMultiplicityResidue m S = ⟨r, hr⟩)
  let target :=
    ((foldMultiplicitySubsetFamily m).filter fun S =>
      foldMultiplicityResidue m S =
        ⟨foldMultiplicityComplementIndex m r,
          Nat.mod_lt _ (foldMultiplicityModulus_pos m)⟩)
  have hcomp_involutive :
      Function.Involutive (fun S : Finset (Fin m) => (Finset.univ : Finset (Fin m)) \ S) := by
    intro S
    ext i
    simp
  have hmem :
      ∀ S : Finset (Fin m),
        S ∈ source ↔ ((Finset.univ : Finset (Fin m)) \ S) ∈ target := by
    intro S
    constructor
    · intro hS
      simp only [source, target, Finset.mem_filter] at hS ⊢
      rcases hS with ⟨_hfamily, hres⟩
      refine ⟨?_, foldMultiplicityResidue_complement m hm S ⟨r, hr⟩ hres⟩
      rw [foldMultiplicitySubsetFamily, Finset.mem_powerset]
      intro i hi
      simp
    · intro hS
      simp only [source, target, Finset.mem_filter] at hS ⊢
      rcases hS with ⟨_hfamily, hres⟩
      refine ⟨?_, ?_⟩
      · rw [foldMultiplicitySubsetFamily, Finset.mem_powerset]
        intro i hi
        simp
      · have hback :=
          foldMultiplicityResidue_complement m hm
            ((Finset.univ : Finset (Fin m)) \ S)
            ⟨foldMultiplicityComplementIndex m r,
              Nat.mod_lt _ (foldMultiplicityModulus_pos m)⟩
            hres
        simpa [foldMultiplicityComplementIndex_involutive m hm r hr] using hback
  unfold Omega.Folding.foldMultiplicityGeneratingPolynomial
  simpa [source, target, foldMultiplicityComplementIndex] using
    Finset.card_bijective
      (fun S : Finset (Fin m) => (Finset.univ : Finset (Fin m)) \ S)
      hcomp_involutive.bijective hmem

end Omega.Folding
