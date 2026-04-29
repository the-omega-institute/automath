import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.SyncKernelWeighted

noncomputable section

/-- The total count `p_n = P_n(1)`. -/
def realInput40ArityChargeTotal {m : ℕ} [NeZero m] (counts : ZMod m → ℝ) : ℝ :=
  ∑ r : ZMod m, counts r

/-- The mean count on the residue classes. -/
def realInput40ArityChargeMean {m : ℕ} [NeZero m] (counts : ZMod m → ℝ) : ℝ :=
  realInput40ArityChargeTotal counts / (m : ℝ)

/-- The centered residue-class energy. -/
def realInput40ArityChargeCenteredEnergy {m : ℕ} [NeZero m] (counts : ZMod m → ℝ) : ℝ :=
  ∑ r : ZMod m, (counts r - realInput40ArityChargeMean counts) ^ 2

/-- The nontrivial Fourier-mode energy. -/
def realInput40ArityChargeFourierEnergy {m : ℕ} [NeZero m] (evals : ZMod m → ℝ) : ℝ :=
  (1 / (m : ℝ)) * Finset.sum (Finset.univ.erase 0) (fun j => evals j ^ 2)

private lemma centered_energy_eq_sum_sq_sub_total_sq_div {m : ℕ} [NeZero m]
    (counts : ZMod m → ℝ) :
    realInput40ArityChargeCenteredEnergy counts =
      (∑ r : ZMod m, counts r ^ 2) -
        realInput40ArityChargeTotal counts ^ 2 / (m : ℝ) := by
  let S : ℝ := realInput40ArityChargeTotal counts
  let μ : ℝ := realInput40ArityChargeMean counts
  have hm : (m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_neZero m).ne'
  have hμ : μ = S / (m : ℝ) := rfl
  unfold realInput40ArityChargeCenteredEnergy
  calc
    ∑ r : ZMod m, (counts r - μ) ^ 2
        = ∑ r : ZMod m, (counts r ^ 2 - (2 * μ) * counts r + μ ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            ring
    _ = (∑ r : ZMod m, counts r ^ 2) - ∑ r : ZMod m, (2 * μ) * counts r +
          ∑ _r : ZMod m, μ ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = (∑ r : ZMod m, counts r ^ 2) - (2 * μ) * S + (m : ℝ) * μ ^ 2 := by
            dsimp [S]
            rw [show (∑ r : ZMod m, (2 * μ) * counts r) = (2 * μ) * ∑ r : ZMod m, counts r by
                  simpa using
                    (Finset.mul_sum (s := Finset.univ) (a := (2 * μ))
                      (f := fun r : ZMod m => counts r)).symm]
            rw [realInput40ArityChargeTotal]
            simp
    _ = (∑ r : ZMod m, counts r ^ 2) - S ^ 2 / (m : ℝ) := by
            rw [hμ]
            field_simp [hm]
            ring

/-- Paper label: `thm:real-input-40-arity-charge-parseval-energy`.
If the discrete Fourier transform of the residue counts has zero mode `P_n(1)` and satisfies the
finite Parseval identity, then the centered congruence-class energy equals the normalized energy
of the nontrivial modes. -/
theorem paper_real_input_40_arity_charge_parseval_energy
    {m : ℕ} [NeZero m] (counts evals : ZMod m → ℝ)
    (hzero : evals 0 = realInput40ArityChargeTotal counts)
    (hparseval : ∑ j : ZMod m, evals j ^ 2 = (m : ℝ) * ∑ r : ZMod m, counts r ^ 2) :
    realInput40ArityChargeCenteredEnergy counts = realInput40ArityChargeFourierEnergy evals := by
  let S : ℝ := realInput40ArityChargeTotal counts
  have hm : (m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_neZero m).ne'
  have hsum_split :
      ∑ j : ZMod m, evals j ^ 2 =
        evals 0 ^ 2 + Finset.sum (Finset.univ.erase 0) (fun j => evals j ^ 2) := by
    simpa [add_comm] using
      (Finset.sum_erase_add (s := Finset.univ) (f := fun j : ZMod m => evals j ^ 2)
        (Finset.mem_univ 0))
  have hnontrivial :
      Finset.sum (Finset.univ.erase 0) (fun j => evals j ^ 2) =
        (m : ℝ) * ∑ r : ZMod m, counts r ^ 2 - S ^ 2 := by
    rw [hsum_split, hzero] at hparseval
    linarith
  rw [realInput40ArityChargeFourierEnergy, centered_energy_eq_sum_sq_sub_total_sq_div]
  rw [hnontrivial]
  field_simp [hm]
  ring

end

end Omega.SyncKernelWeighted
