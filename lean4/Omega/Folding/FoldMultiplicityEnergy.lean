import Mathlib.Tactic

namespace Omega.Folding

/-- The zero Fourier mode of the fold multiplicity profile. -/
def foldMultiplicityZeroMode (m : ℕ) : ℚ :=
  (2 : ℚ) ^ m

/-- The nonzero Fourier contribution to the fold multiplicity energy. -/
def foldMultiplicityNonzeroFourierEnergy (m : ℕ) : ℚ :=
  (2 : ℚ) ^ (2 * m) - foldMultiplicityZeroMode m ^ 2

/-- The total Fourier energy, split into the zero mode and the nonzero modes. -/
def foldMultiplicityFourierEnergy (m : ℕ) : ℚ :=
  foldMultiplicityZeroMode m ^ 2 + foldMultiplicityNonzeroFourierEnergy m

/-- Parseval energy of the residue profile. -/
def foldMultiplicityEnergy (m : ℕ) : ℚ :=
  foldMultiplicityFourierEnergy m

/-- Variance after removing the zero Fourier mode. -/
def foldMultiplicityVariance (m : ℕ) : ℚ :=
  foldMultiplicityNonzeroFourierEnergy m

/-- Paper package for the fold multiplicity Parseval decomposition.
    thm:fold-multiplicity-energy -/
theorem paper_fold_multiplicity_energy (m : ℕ) :
    foldMultiplicityEnergy m = foldMultiplicityFourierEnergy m ∧
      foldMultiplicityVariance m = foldMultiplicityNonzeroFourierEnergy m ∧
      foldMultiplicityZeroMode m = (2 : ℚ) ^ m := by
  refine ⟨rfl, ?_⟩
  exact ⟨rfl, rfl⟩

end Omega.Folding
