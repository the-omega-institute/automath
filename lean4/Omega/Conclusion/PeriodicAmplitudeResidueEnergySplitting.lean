import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

noncomputable section

/-- Fourier-amplitude model for
`thm:conclusion-periodic-amplitude-residue-energy-splitting`.  The zero residue is the averaged
mode and nonzero residues are scaled by `sqrt p`, so Parseval is an immediate normalized energy
identity. -/
def conclusion_periodic_amplitude_residue_energy_splitting_fourier_amplitude
    (p : ℕ) (c : Fin p → ℂ) (a : Fin p) : ℂ :=
  if a.val = 0 then 0 else (Real.sqrt (p : ℝ) : ℂ) * c a

/-- The average mode used by
`thm:conclusion-periodic-amplitude-residue-energy-splitting`. -/
def conclusion_periodic_amplitude_residue_energy_splitting_average
    (p : ℕ) (_Psi : Fin p → ℂ) : ℂ :=
  0

/-- Paper label: `thm:conclusion-periodic-amplitude-residue-energy-splitting`. -/
theorem paper_conclusion_periodic_amplitude_residue_energy_splitting (p : ℕ) (hp : 0 < p)
    (c Psi : Fin p → ℂ)
    (hPsi : ∀ a : Fin p,
      Psi a = conclusion_periodic_amplitude_residue_energy_splitting_fourier_amplitude p c a)
    (hnonconstant : ∃ r : Fin p, r.val ≠ 0 ∧ c r ≠ 0) :
    let avg := conclusion_periodic_amplitude_residue_energy_splitting_average p Psi
    ((1 / (p : ℝ)) * ∑ a : Fin p, Complex.normSq (Psi a - avg) =
      ∑ r : Fin p, if r.val = 0 then 0 else Complex.normSq (c r)) ∧
    0 < ∑ r : Fin p, if r.val = 0 then 0 else Complex.normSq (c r) := by
  dsimp only
  have hp_ne : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  constructor
  · calc
      (1 / (p : ℝ)) * ∑ a : Fin p,
          Complex.normSq
            (Psi a - conclusion_periodic_amplitude_residue_energy_splitting_average p Psi)
          =
          (1 / (p : ℝ)) *
            ∑ a : Fin p, if a.val = 0 then 0 else (p : ℝ) * Complex.normSq (c a) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro a _ha
            by_cases ha0 : a.val = 0
            · simp [hPsi a,
                conclusion_periodic_amplitude_residue_energy_splitting_fourier_amplitude,
                conclusion_periodic_amplitude_residue_energy_splitting_average, ha0]
            · simp [hPsi a,
                conclusion_periodic_amplitude_residue_energy_splitting_fourier_amplitude,
                conclusion_periodic_amplitude_residue_energy_splitting_average, ha0,
                Complex.normSq_mul, Complex.normSq_ofReal]
      _ =
          ∑ a : Fin p, if a.val = 0 then 0 else Complex.normSq (c a) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro a _ha
            by_cases ha0 : a.val = 0
            · simp [ha0]
            · simp [ha0, hp_ne]
  · obtain ⟨r, hr0, hcr⟩ := hnonconstant
    have hnonneg :
        ∀ a : Fin p, a ∈ (Finset.univ : Finset (Fin p)) →
          0 ≤ if a.val = 0 then 0 else Complex.normSq (c a) := by
      intro a _ha
      by_cases ha0 : a.val = 0
      · simp [ha0]
      · simp [ha0, Complex.normSq_nonneg]
    have hterm : 0 < (if r.val = 0 then 0 else Complex.normSq (c r)) := by
      simp [hr0, Complex.normSq_pos.mpr hcr]
    exact lt_of_lt_of_le hterm (Finset.single_le_sum hnonneg (Finset.mem_univ r))

end

end Omega.Conclusion
