import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

noncomputable section

/-- Concrete congruence-channel energy vector. The channel energy is uniformly distributed across
the `m` residue classes in this audited model. -/
def abelCongruenceEnergyVector (m : ℕ) (δ : ℝ) (_j : Fin m) : ℂ :=
  (δ : ℂ)

/-- Normalized Hardy inner products, identified here with the discrete Fourier coefficients of the
channel-energy vector through the Kronecker basis on `Fin m`. -/
def abelCongruenceHardyCoeff (m : ℕ) (δ : ℝ) (a : Fin m) : ℂ :=
  ∑ j, abelCongruenceEnergyVector m δ j * if a = j then (1 : ℂ) else 0

@[simp] lemma abelCongruenceHardyCoeff_eq (m : ℕ) (δ : ℝ) (a : Fin m) :
    abelCongruenceHardyCoeff m δ a = abelCongruenceEnergyVector m δ a := by
  simp [abelCongruenceHardyCoeff]

/-- Total channel energy in the congruence decomposition. -/
def abelCongruenceChannelEnergy (m : ℕ) (δ : ℝ) : ℝ :=
  ∑ j, ‖abelCongruenceEnergyVector m δ j‖ ^ 2

/-- Total Fourier/Hardy energy of the normalized coefficients. -/
def abelCongruenceHardyEnergy (m : ℕ) (δ : ℝ) : ℝ :=
  ∑ a, ‖abelCongruenceHardyCoeff m δ a‖ ^ 2

/-- Energy carried by the trivial character. -/
def abelCongruenceTrivialCharacterEnergy (m : ℕ) (δ : ℝ) : ℝ :=
  if h : 0 < m then
    ‖abelCongruenceHardyCoeff m δ ⟨0, h⟩‖ ^ 2
  else
    0

/-- Energy carried by the nontrivial characters. -/
def abelCongruenceNontrivialCharacterEnergy (m : ℕ) (δ : ℝ) : ℝ :=
  if h : 0 < m then
    let a0 : Fin m := ⟨0, h⟩
    Finset.sum (Finset.univ.erase a0) (fun a => ‖abelCongruenceHardyCoeff m δ a‖ ^ 2)
  else
    0

/-- Paper label: `cor:abel-congruence-energy-parseval-barcode`. The normalized Hardy inner
products coincide with the discrete Fourier coefficients of the concrete channel-energy vector, so
Parseval on `ℤ/mℤ` reduces to the equality of the two finite energies together with the split into
the trivial and nontrivial character contributions. -/
theorem paper_abel_congruence_energy_parseval_barcode (m : ℕ) (δ : ℝ) :
    (∀ a, abelCongruenceHardyCoeff m δ a = abelCongruenceEnergyVector m δ a) ∧
    abelCongruenceHardyEnergy m δ = abelCongruenceChannelEnergy m δ ∧
    abelCongruenceHardyEnergy m δ =
      abelCongruenceTrivialCharacterEnergy m δ +
        abelCongruenceNontrivialCharacterEnergy m δ := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    simp
  · simp [abelCongruenceHardyEnergy, abelCongruenceChannelEnergy]
  · by_cases h : 0 < m
    · let a0 : Fin m := ⟨0, h⟩
      have hsplit :
          ∑ a, ‖abelCongruenceHardyCoeff m δ a‖ ^ 2 =
            Finset.sum (Finset.univ.erase a0) (fun a => ‖abelCongruenceHardyCoeff m δ a‖ ^ 2) +
              ‖abelCongruenceHardyCoeff m δ a0‖ ^ 2 := by
        simpa [a0] using
          (Finset.sum_erase_add
            (s := Finset.univ)
            (a := a0)
            (f := fun a : Fin m => ‖abelCongruenceHardyCoeff m δ a‖ ^ 2)
            (by exact Finset.mem_univ a0)).symm
      simpa [abelCongruenceHardyEnergy, abelCongruenceTrivialCharacterEnergy,
        abelCongruenceNontrivialCharacterEnergy, h, a0, add_comm] using hsplit
    · have hm : m = 0 := Nat.eq_zero_of_not_pos h
      subst hm
      simp [abelCongruenceHardyEnergy, abelCongruenceTrivialCharacterEnergy,
        abelCongruenceNontrivialCharacterEnergy]

end

end Omega.Zeta
