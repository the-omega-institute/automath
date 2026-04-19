import Mathlib.Tactic
import Omega.SPG.HypercubeCycleLatticeDirectsumCounting

namespace Omega.SPG

noncomputable section

/-- Number of words over an `alphabetSize`-letter alphabet of length at most `L`. -/
def wordsUpToLength (alphabetSize : ℕ) : ℕ → ℕ
  | 0 => 1
  | L + 1 => wordsUpToLength alphabetSize L + alphabetSize ^ (L + 1)

/-- The direct-sum cycle-lattice counting term converted to a base-`alphabetSize` description
length scale. -/
def directsumMDLLowerBound (D : HypercubeCycleLatticeDirectsumData) (alphabetSize : ℕ) : ℝ :=
  directsumCountingTerm D / Real.log alphabetSize

/-- Concrete MDL package for the direct sum of identical hypercube cycle lattices: the explicit
counting term from the direct-sum asymptotic, positivity of the code alphabet logarithm, the
standard upper bound on words of bounded length, and the resulting base-`alphabetSize` lower-bound
normalization. -/
def HypercubeCycleLatticeDirectsumMDLLaw
    (D : HypercubeCycleLatticeDirectsumData) (alphabetSize : ℕ) : Prop :=
  directsumCountingTerm D =
      (D.m * D.rank : ℝ) * Real.log D.radius - ((D.m : ℝ) / 2) * Real.log D.treeCount ∧
    0 < Real.log alphabetSize ∧
    (∀ L : ℕ, wordsUpToLength alphabetSize L ≤ alphabetSize ^ (L + 1)) ∧
    directsumMDLLowerBound D alphabetSize =
      ((D.m * D.rank : ℝ) * Real.log D.radius - ((D.m : ℝ) / 2) * Real.log D.treeCount) /
        Real.log alphabetSize

private theorem wordsUpToLength_le_pow_succ (alphabetSize L : ℕ) (hAlphabet : 2 ≤ alphabetSize) :
    wordsUpToLength alphabetSize L ≤ alphabetSize ^ (L + 1) := by
  induction L with
  | zero =>
      simpa [wordsUpToLength] using le_trans (by decide : 1 ≤ 2) hAlphabet
  | succ L ih =>
      calc
        wordsUpToLength alphabetSize (L + 1) =
            wordsUpToLength alphabetSize L + alphabetSize ^ (L + 1) := by
              simp [wordsUpToLength]
        _ ≤ alphabetSize ^ (L + 1) + alphabetSize ^ (L + 1) := by
              simpa [add_comm, add_left_comm, add_assoc] using
                Nat.add_le_add_left ih (alphabetSize ^ (L + 1))
        _ = 2 * alphabetSize ^ (L + 1) := by ring
        _ ≤ alphabetSize * alphabetSize ^ (L + 1) := by
              exact Nat.mul_le_mul_right (alphabetSize ^ (L + 1)) hAlphabet
        _ = alphabetSize ^ (L + 2) := by
              symm
              rw [Nat.pow_succ']
        _ = alphabetSize ^ ((L + 1) + 1) := by ring

/-- Combining the explicit direct-sum counting law with the standard bound on the number of words
of length at most `L` yields the corresponding base-`alphabetSize` description-length lower-bound
normalization.
    cor:hypercube-cycle-lattice-directsum-mdl -/
theorem paper_hypercube_cycle_lattice_directsum_mdl (D : HypercubeCycleLatticeDirectsumData)
    (alphabetSize : ℕ) (hAlphabet : 2 ≤ alphabetSize) :
    HypercubeCycleLatticeDirectsumMDLLaw D alphabetSize := by
  rcases paper_hypercube_cycle_lattice_directsum_counting D with
    ⟨_, _, _, _, hExplicit⟩
  have hAlphabetReal : (1 : ℝ) < alphabetSize := by
    exact_mod_cast lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hAlphabet
  have hLog : 0 < Real.log alphabetSize := Real.log_pos hAlphabetReal
  refine ⟨hExplicit, hLog, ?_, ?_⟩
  · intro L
    exact wordsUpToLength_le_pow_succ alphabetSize L hAlphabet
  unfold directsumMDLLowerBound
  rw [hExplicit]

end

end Omega.SPG
