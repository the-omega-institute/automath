import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The centered residue vector, scaled by the modulus so that all coordinates are integral. -/
def atomicCenteredResidueVector (m : Nat) (ℓ : Fin m) : Fin m → ℤ :=
  fun r => if r = ℓ then (2 : ℤ) * m - 2 else -2

/-- The ambient dot product on the residue-coordinate space. -/
def atomicCenteredResidueInner {m : Nat} (x y : Fin m → ℤ) : ℤ :=
  ∑ r, x r * y r

/-- Concrete regular-simplex certificate for a family of centered residue vectors: every vector has
zero coordinate sum, and the Gram matrix has constant diagonal and constant off-diagonal entries. -/
def IsRegularSimplexFamily {m : Nat} (v : Fin m → Fin m → ℤ) : Prop :=
  (∀ i, ∑ r, v i r = 0) ∧
    ∀ i j,
      atomicCenteredResidueInner (v i) (v j) =
        if i = j then (4 : ℤ) * m * (m - 1) else -(4 * m : ℤ)

private lemma card_univ_erase {m : Nat} (i : Fin m) :
    (Finset.univ.erase i).card = m - 1 := by
  have h :
      (Finset.univ.erase i).card + 1 = m := by
    simpa using Finset.card_erase_add_one (s := (Finset.univ : Finset (Fin m))) (a := i)
      (by simp)
  omega

private lemma card_univ_erase_erase {m : Nat} (i j : Fin m) (hij : i ≠ j) :
    ((Finset.univ.erase i).erase j).card = m - 2 := by
  have hji : j ≠ i := by
    simpa using hij.symm
  have hj_mem : j ∈ Finset.univ.erase i := by
    simp [hji]
  have h :
      ((Finset.univ.erase i).erase j).card + 1 = (Finset.univ.erase i).card := by
    simpa using Finset.card_erase_add_one (s := Finset.univ.erase i) (a := j) hj_mem
  have h' : ((Finset.univ.erase i).erase j).card + 1 = m - 1 := by
    simpa [card_univ_erase i] using h
  omega

private lemma sum_atomicCenteredResidueVector {m : Nat} (i : Fin m) :
    ∑ r, atomicCenteredResidueVector m i r = 0 := by
  have hsplit :
      ∑ r, atomicCenteredResidueVector m i r =
        Finset.sum (Finset.univ.erase i) (fun r => atomicCenteredResidueVector m i r) +
          atomicCenteredResidueVector m i i := by
    exact
      (Finset.sum_erase_add
        (s := (Finset.univ : Finset (Fin m)))
        (a := i)
        (f := fun r => atomicCenteredResidueVector m i r)
        (by exact Finset.mem_univ i)).symm
  have hconst :
      Finset.sum (Finset.univ.erase i) (fun r => atomicCenteredResidueVector m i r) =
        ((Finset.univ.erase i).card : ℤ) * (-2) := by
    calc
      Finset.sum (Finset.univ.erase i) (fun r => atomicCenteredResidueVector m i r)
          = Finset.sum (Finset.univ.erase i) (fun _ : Fin m => (-2 : ℤ)) := by
              apply Finset.sum_congr rfl
              intro (r : Fin m) hr
              have hri : r ≠ i := by
                exact (Finset.mem_erase.mp hr).1
              simp [atomicCenteredResidueVector, hri]
      _ = ((Finset.univ.erase i).card : ℤ) * (-2) := by
            simp [Finset.sum_const]
  have hcard : ((Finset.univ.erase i).card : ℤ) = (m : ℤ) - 1 := by
    rw [card_univ_erase (m := m) i]
    have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le i.1) i.2
    have hm1 : 1 ≤ m := Nat.succ_le_of_lt hmpos
    have hm1z : (1 : ℤ) ≤ m := by exact_mod_cast hm1
    omega
  rw [hsplit, hconst, hcard]
  simp [atomicCenteredResidueVector]
  omega

private lemma inner_atomicCenteredResidueVector_self {m : Nat} (i : Fin m) :
    atomicCenteredResidueInner (atomicCenteredResidueVector m i) (atomicCenteredResidueVector m i) =
      4 * m * (m - 1) := by
  have hsplit :
      atomicCenteredResidueInner (atomicCenteredResidueVector m i) (atomicCenteredResidueVector m i) =
        Finset.sum (Finset.univ.erase i)
            (fun r => atomicCenteredResidueVector m i r * atomicCenteredResidueVector m i r) +
          atomicCenteredResidueVector m i i * atomicCenteredResidueVector m i i := by
    unfold atomicCenteredResidueInner
    exact
      (Finset.sum_erase_add
        (s := (Finset.univ : Finset (Fin m)))
        (a := i)
        (f := fun r => atomicCenteredResidueVector m i r * atomicCenteredResidueVector m i r)
        (by exact Finset.mem_univ i)).symm
  have hconst :
      Finset.sum (Finset.univ.erase i)
          (fun r => atomicCenteredResidueVector m i r * atomicCenteredResidueVector m i r) =
        ((Finset.univ.erase i).card : ℤ) * 4 := by
    calc
      Finset.sum (Finset.univ.erase i)
          (fun r => atomicCenteredResidueVector m i r * atomicCenteredResidueVector m i r)
          = Finset.sum (Finset.univ.erase i) (fun _ : Fin m => (4 : ℤ)) := by
              apply Finset.sum_congr rfl
              intro (r : Fin m) hr
              have hri : r ≠ i := by
                exact (Finset.mem_erase.mp hr).1
              simp [atomicCenteredResidueVector, hri]
      _ = ((Finset.univ.erase i).card : ℤ) * 4 := by
            simp [Finset.sum_const]
  have hcard : ((Finset.univ.erase i).card : ℤ) = (m : ℤ) - 1 := by
    rw [card_univ_erase (m := m) i]
    have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le i.1) i.2
    have hm1 : 1 ≤ m := Nat.succ_le_of_lt hmpos
    have hm1z : (1 : ℤ) ≤ m := by exact_mod_cast hm1
    omega
  rw [hsplit, hconst, hcard]
  simp [atomicCenteredResidueVector]
  ring_nf

private lemma inner_atomicCenteredResidueVector_ne {m : Nat} (i j : Fin m) (hij : i ≠ j) :
    atomicCenteredResidueInner (atomicCenteredResidueVector m i) (atomicCenteredResidueVector m j) =
      -(4 * m : ℤ) := by
  have hsplit :
      atomicCenteredResidueInner (atomicCenteredResidueVector m i) (atomicCenteredResidueVector m j) =
        Finset.sum (Finset.univ.erase i)
            (fun r => atomicCenteredResidueVector m i r * atomicCenteredResidueVector m j r) +
          atomicCenteredResidueVector m i i * atomicCenteredResidueVector m j i := by
    unfold atomicCenteredResidueInner
    exact
      (Finset.sum_erase_add
        (s := (Finset.univ : Finset (Fin m)))
        (a := i)
        (f := fun r => atomicCenteredResidueVector m i r * atomicCenteredResidueVector m j r)
        (by exact Finset.mem_univ i)).symm
  have hji : j ≠ i := by
    simpa using hij.symm
  have hj_mem : j ∈ Finset.univ.erase i := by
    simp [hji]
  have hsplit' :
      Finset.sum (Finset.univ.erase i)
          (fun r => atomicCenteredResidueVector m i r * atomicCenteredResidueVector m j r) =
        Finset.sum ((Finset.univ.erase i).erase j)
            (fun r => atomicCenteredResidueVector m i r * atomicCenteredResidueVector m j r) +
          atomicCenteredResidueVector m i j * atomicCenteredResidueVector m j j := by
    simpa using
      (Finset.sum_erase_add
        (s := Finset.univ.erase i)
        (a := j)
        (f := fun r => atomicCenteredResidueVector m i r * atomicCenteredResidueVector m j r)
        hj_mem).symm
  have hconst :
      Finset.sum ((Finset.univ.erase i).erase j)
          (fun r => atomicCenteredResidueVector m i r * atomicCenteredResidueVector m j r) =
        (((Finset.univ.erase i).erase j).card : ℤ) * 4 := by
    calc
      Finset.sum ((Finset.univ.erase i).erase j)
          (fun r => atomicCenteredResidueVector m i r * atomicCenteredResidueVector m j r)
          = Finset.sum ((Finset.univ.erase i).erase j) (fun _ : Fin m => (4 : ℤ)) := by
              apply Finset.sum_congr rfl
              intro (r : Fin m) hr
              have hri : r ≠ i := by
                exact (Finset.mem_erase.mp (Finset.mem_of_mem_erase hr)).1
              have hrj : r ≠ j := by
                exact (Finset.mem_erase.mp hr).1
              simp [atomicCenteredResidueVector, hri, hrj]
      _ = (((Finset.univ.erase i).erase j).card : ℤ) * 4 := by
            simp [Finset.sum_const]
  have hcard : ((((Finset.univ.erase i).erase j).card : ℤ)) = (m : ℤ) - 2 := by
    rw [card_univ_erase_erase (m := m) i j hij]
    have hm2 : 2 ≤ m := by
      by_contra hm2
      have hm' : m ≤ 1 := by omega
      have hEq : i = j := by
        apply Fin.ext
        omega
      exact hij hEq
    have hm2z : (2 : ℤ) ≤ m := by exact_mod_cast hm2
    omega
  rw [hsplit, hsplit', hconst, hcard]
  have hij' : i ≠ j := hij
  have hji' : j ≠ i := by simpa using hij.symm
  simp [atomicCenteredResidueVector, hij', hji']
  omega

/-- Paper label: `thm:xi-time-part65c-atomic-centered-residue-simplex`. The integral, centered
residue vectors have zero coordinate sum and the exact regular-simplex Gram matrix. -/
theorem paper_xi_time_part65c_atomic_centered_residue_simplex (m : Nat) (hm : 2 <= m) :
    IsRegularSimplexFamily (atomicCenteredResidueVector m) := by
  let _ := hm
  refine ⟨sum_atomicCenteredResidueVector, ?_⟩
  intro i j
  by_cases hij : i = j
  · subst hij
    simpa using inner_atomicCenteredResidueVector_self (m := m) i
  · simp [inner_atomicCenteredResidueVector_ne, hij]

private lemma xi_time_part65c_atomic_centered_residue_isotropic_inner_vector
    (m : Nat) (v : Fin m → ℤ) (ℓ : Fin m) :
    atomicCenteredResidueInner v (atomicCenteredResidueVector m ℓ) =
      (2 : ℤ) * (m : ℤ) * v ℓ - 2 * ∑ r, v r := by
  unfold atomicCenteredResidueInner atomicCenteredResidueVector
  calc
    ∑ r : Fin m, v r * (if r = ℓ then (2 : ℤ) * m - 2 else -2)
        = ∑ r : Fin m, (-2 * v r + if r = ℓ then (2 : ℤ) * (m : ℤ) * v r else 0) := by
            apply Finset.sum_congr rfl
            intro r hr
            by_cases h : r = ℓ
            · simp [h]
              ring
            · simp [h]
              ring
    _ = -2 * ∑ r : Fin m, v r +
          ∑ r : Fin m, if r = ℓ then (2 : ℤ) * (m : ℤ) * v r else 0 := by
            simp [Finset.sum_add_distrib, Finset.mul_sum]
    _ = (2 : ℤ) * (m : ℤ) * v ℓ - 2 * ∑ r, v r := by
            have hsingle :
                (∑ r : Fin m, if r = ℓ then (2 : ℤ) * (m : ℤ) * v r else 0) =
                  (2 : ℤ) * (m : ℤ) * v ℓ := by
              rw [Fintype.sum_eq_single ℓ]
              · simp only [↓reduceIte]
              · intro r hr
                simp [hr]
            rw [hsingle]
            ring

/-- cor:xi-time-part65c-atomic-centered-residue-isotropic -/
theorem paper_xi_time_part65c_atomic_centered_residue_isotropic (m : Nat) (hm : 2 <= m)
    (v : Fin m → ℤ) (hv : ∑ r, v r = 0) :
    ∑ ℓ : Fin m, atomicCenteredResidueInner v (atomicCenteredResidueVector m ℓ) ^ (2 : Nat) =
      (4 : ℤ) * (m : ℤ) ^ (2 : Nat) * atomicCenteredResidueInner v v := by
  let _ := hm
  have hinner :
      ∀ ℓ : Fin m, atomicCenteredResidueInner v (atomicCenteredResidueVector m ℓ) =
        (2 : ℤ) * (m : ℤ) * v ℓ := by
    intro ℓ
    rw [xi_time_part65c_atomic_centered_residue_isotropic_inner_vector, hv]
    ring
  calc
    ∑ ℓ : Fin m, atomicCenteredResidueInner v (atomicCenteredResidueVector m ℓ) ^ (2 : Nat)
        = ∑ ℓ : Fin m, ((2 : ℤ) * (m : ℤ) * v ℓ) ^ (2 : Nat) := by
            apply Finset.sum_congr rfl
            intro ℓ hℓ
            rw [hinner]
    _ = (4 : ℤ) * (m : ℤ) ^ (2 : Nat) * ∑ ℓ : Fin m, v ℓ * v ℓ := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ℓ hℓ
            ring
    _ = (4 : ℤ) * (m : ℤ) ^ (2 : Nat) * atomicCenteredResidueInner v v := by
            simp [atomicCenteredResidueInner, pow_two]

end Omega.Zeta
