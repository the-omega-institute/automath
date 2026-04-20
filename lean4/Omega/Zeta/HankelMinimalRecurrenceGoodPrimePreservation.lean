import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic
import Omega.Zeta.HankelMaximalMinorSyndromeNormalFormUniqueness

namespace Omega.Zeta

open Matrix
open scoped BigOperators

/-- Pad a degree-`r` coefficient vector to length `d` by extending it with zeros. -/
def hankelPadCoeffs {k : Type*} [Field k] {r d : ℕ} (_hr : r < d) (q : Fin (r + 1) → k) :
    Fin d → k :=
  fun i =>
    if hi : i.1 < r + 1 then
      q ⟨i.1, hi⟩
    else
      0

private lemma hankelPadCoeffs_eq_zero_tail {k : Type*} [Field k] {r d : ℕ} (hr : r < d)
    (q : Fin (r + 1) → k) {j : ℕ} (hj₁ : r + 1 ≤ j) (hj₂ : j < d) :
    hankelPadCoeffs hr q ⟨j, hj₂⟩ = 0 := by
  simp [hankelPadCoeffs, Nat.not_lt.mpr hj₁]

private lemma hankelPrincipal_mulVec_pad_eq_zero {p d r : ℕ} [Fact p.Prime]
    (a : ℕ → ZMod p) (hr : r < d) (q : Fin (r + 1) → ZMod p)
    (hqrec : hankelRecurrence a q) :
    (hankelPrincipal a d).mulVec (hankelPadCoeffs hr q) = 0 := by
  ext i
  change ((hankelPrincipal a d).mulVec (hankelPadCoeffs hr q)) i = 0
  change ∑ j : Fin d, a (i.1 + j.1) * hankelPadCoeffs hr q j = 0
  let g : ℕ → ZMod p := fun j =>
    if hj : j < d then
      a (i.1 + j) * hankelPadCoeffs hr q ⟨j, hj⟩
    else
      0
  have hsum :
      (∑ j : Fin d, a (i.1 + j.1) * hankelPadCoeffs hr q j) =
        ∑ j ∈ Finset.range d, g j := by
    simpa [g] using (Fin.sum_univ_eq_sum_range g d)
  rw [hsum]
  calc
    ∑ j ∈ Finset.range d, g j = ∑ j ∈ Finset.range (r + 1), g j + ∑ j ∈ Finset.Ico (r + 1) d, g j := by
      symm
      exact Finset.sum_range_add_sum_Ico g (Nat.succ_le_of_lt hr)
    _ = ∑ j ∈ Finset.range (r + 1), g j := by
      have htailsum : ∑ j ∈ Finset.Ico (r + 1) d, g j = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rcases Finset.mem_Ico.mp hj with ⟨hj₁, hj₂⟩
        have htail : hankelPadCoeffs hr q ⟨j, hj₂⟩ = 0 :=
          hankelPadCoeffs_eq_zero_tail hr q hj₁ hj₂
        simp [g, hj₂, htail]
      rw [htailsum, add_zero]
    _ = 0 := by
      let h : ℕ → ZMod p := fun j =>
        if hj : j < r + 1 then
          q ⟨j, hj⟩ * a (i.1 + j)
        else
          0
      have hgh : ∑ j ∈ Finset.range (r + 1), g j = ∑ j ∈ Finset.range (r + 1), h j := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjr : j < r + 1 := Finset.mem_range.mp hj
        have hjd : j < d := lt_of_lt_of_le hjr (Nat.succ_le_of_lt hr)
        simp [g, h, hankelPadCoeffs, hjd, mul_comm]
      rw [hgh]
      have hh :
          ∑ j ∈ Finset.range (r + 1), h j = ∑ j : Fin (r + 1), q j * a (i.1 + j.1) := by
        calc
          ∑ j ∈ Finset.range (r + 1), h j = ∑ j : Fin (r + 1), h j := by
            symm
            exact Fin.sum_univ_eq_sum_range h (r + 1)
          _ = ∑ j : Fin (r + 1), q j * a (i.1 + j.1) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hjlt : (j : ℕ) < r + 1 := j.2
            have hjle : (j : ℕ) ≤ r := Nat.lt_succ_iff.mp hjlt
            simp [h, hjle]
      rw [hh]
      exact hqrec i.1

private lemma hankelPadCoeffs_eq_zero_of_principal_det_ne_zero {p d r : ℕ} [Fact p.Prime]
    (a : ℕ → ZMod p) (hr : r < d) (q : Fin (r + 1) → ZMod p)
    (hqrec : hankelRecurrence a q)
    (hdet : (hankelPrincipal a d).det ≠ 0) :
    hankelPadCoeffs hr q = 0 := by
  let M := hankelPrincipal a d
  have hker : M.mulVec (hankelPadCoeffs hr q) = 0 :=
    hankelPrincipal_mulVec_pad_eq_zero a hr q hqrec
  have hsmul : M.det • hankelPadCoeffs hr q = 0 := by
    calc
      M.det • hankelPadCoeffs hr q = (M.det • (1 : Matrix (Fin d) (Fin d) (ZMod p))).mulVec
          (hankelPadCoeffs hr q) := by
            simp [Matrix.smul_mulVec, Matrix.one_mulVec]
      _ = (M.adjugate * M).mulVec (hankelPadCoeffs hr q) := by
            rw [Matrix.adjugate_mul]
      _ = M.adjugate.mulVec (M.mulVec (hankelPadCoeffs hr q)) := by
            rw [Matrix.mulVec_mulVec]
      _ = 0 := by simp [hker]
  ext i
  have hi := congrFun hsmul i
  exact (mul_eq_zero.mp hi).resolve_left hdet

/-- For an integral Hankel recurrence whose leading coefficient stays nonzero mod `p`, the reduced
monic recurrence survives modulo `p`; if the reduced principal Hankel block is invertible, no
shorter monic recurrence can appear after reduction.
    cor:xi-hankel-minimal-recurrence-good-prime-preservation -/
theorem paper_xi_hankel_minimal_recurrence_good_prime_preservation
    (d p : ℕ) [Fact p.Prime] (a : ℕ → ℤ) (Δ : Fin (d + 1) → ℤ)
    (hrec : ∀ n, ∑ j : Fin (d + 1), Δ j * a (n + j.1) = 0)
    (hgood : (((Δ (Fin.last d) : ℤ) : ZMod p) ≠ 0))
    (hdet : (hankelPrincipal (fun n => ((a n : ℤ) : ZMod p)) d).det ≠ 0) :
    hankelRecurrence
        (fun n => ((a n : ℤ) : ZMod p))
        (fun j => (((Δ j : ℤ) : ZMod p) / (((Δ (Fin.last d) : ℤ) : ZMod p)))) ∧
      (fun j => (((Δ j : ℤ) : ZMod p) / (((Δ (Fin.last d) : ℤ) : ZMod p)))) (Fin.last d) = 1 ∧
      ∀ r < d, ∀ q : Fin (r + 1) → ZMod p, q (Fin.last r) = 1 →
        ¬ hankelRecurrence (fun n => ((a n : ℤ) : ZMod p)) q := by
  let abar : ℕ → ZMod p := fun n => ((a n : ℤ) : ZMod p)
  let cbar : ZMod p := ((Δ (Fin.last d) : ℤ) : ZMod p)
  let qbar : Fin (d + 1) → ZMod p := fun j => ((Δ j : ℤ) : ZMod p) / cbar
  have hrec_mod : ∀ n, ∑ j : Fin (d + 1), ((Δ j : ℤ) : ZMod p) * abar (n + j.1) = 0 := by
    intro n
    simpa [abar] using congrArg (fun z : ℤ => ((z : ℤ) : ZMod p)) (hrec n)
  have hqbar_rec : hankelRecurrence abar qbar := by
    intro n
    calc
      ∑ j : Fin (d + 1), qbar j * abar (n + j.1)
          = cbar⁻¹ * ∑ j : Fin (d + 1), ((Δ j : ℤ) : ZMod p) * abar (n + j.1) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j hj
              simp [qbar, cbar, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      _ = 0 := by rw [hrec_mod n, mul_zero]
  have hqbar_monic : qbar (Fin.last d) = 1 := by
    simp [qbar, cbar, hgood]
  refine ⟨hqbar_rec, hqbar_monic, ?_⟩
  intro r hr q hqmonic hqrec
  have hpad_zero :
      hankelPadCoeffs hr q = 0 :=
    hankelPadCoeffs_eq_zero_of_principal_det_ne_zero abar hr q hqrec hdet
  have hlast_zero : hankelPadCoeffs hr q ⟨r, hr⟩ = 0 := by
    have h := congrFun hpad_zero ⟨r, hr⟩
    simpa using h
  have hlast_one : hankelPadCoeffs hr q ⟨r, hr⟩ = 1 := by
    simpa [hankelPadCoeffs] using hqmonic
  have hcontr : (0 : ZMod p) = 1 := hlast_zero.symm.trans hlast_one
  exact zero_ne_one hcontr

end Omega.Zeta
