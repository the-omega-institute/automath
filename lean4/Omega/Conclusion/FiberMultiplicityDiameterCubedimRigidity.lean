import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.POM.FiberReconstructionCartesianProduct

namespace Omega.Conclusion

open scoped goldenRatio

noncomputable section

/-- The multiplicity attached to a path-length decomposition. -/
def conclusion_fiber_multiplicity_diameter_cubedim_rigidity_multiplicity
    (lengths : List ℕ) : ℝ :=
  ((lengths.map fun ell => Nat.fib (ell + 2)).prod : ℝ)

private lemma conclusion_fiber_multiplicity_diameter_cubedim_rigidity_fib_lower_phi_pow_pair :
    ∀ n : ℕ,
      Real.goldenRatio ^ n ≤ (Nat.fib (n + 2) : ℝ) ∧
        Real.goldenRatio ^ (n + 1) ≤ (Nat.fib (n + 3) : ℝ)
  | 0 => by
      constructor
      · simp
      · have hphi_lt_two : Real.goldenRatio < (2 : ℝ) := Real.goldenRatio_lt_two
        norm_num [Nat.fib]
        linarith
  | n + 1 => by
      rcases conclusion_fiber_multiplicity_diameter_cubedim_rigidity_fib_lower_phi_pow_pair n with
        ⟨hn, hn1⟩
      constructor
      · exact hn1
      · have hphi_rec :
          Real.goldenRatio ^ (n + 2) =
            Real.goldenRatio ^ n + Real.goldenRatio ^ (n + 1) := by
          calc
            Real.goldenRatio ^ (n + 2) = Real.goldenRatio ^ n * Real.goldenRatio ^ 2 := by
              simp [pow_add]
            _ = Real.goldenRatio ^ n * (Real.goldenRatio + 1) := by
              rw [Real.goldenRatio_sq]
            _ = Real.goldenRatio ^ n + Real.goldenRatio ^ (n + 1) := by
              ring
        have hfib_nat : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            (Nat.fib_add_two (n := n + 2))
        have hfib :
            (Nat.fib (n + 4) : ℝ) = Nat.fib (n + 2) + Nat.fib (n + 3) := by
          exact_mod_cast hfib_nat
        calc
          Real.goldenRatio ^ (n + 2) =
              Real.goldenRatio ^ n + Real.goldenRatio ^ (n + 1) := hphi_rec
          _ ≤ (Nat.fib (n + 2) : ℝ) + Nat.fib (n + 3) := by gcongr
          _ = (Nat.fib (n + 4) : ℝ) := by simpa [add_comm] using hfib.symm

private lemma conclusion_fiber_multiplicity_diameter_cubedim_rigidity_fib_lower_phi_pow
    (n : ℕ) :
    Real.goldenRatio ^ n ≤ (Nat.fib (n + 2) : ℝ) :=
  (conclusion_fiber_multiplicity_diameter_cubedim_rigidity_fib_lower_phi_pow_pair n).1

private lemma conclusion_fiber_multiplicity_diameter_cubedim_rigidity_fib_upper_phi_pow_pair :
    ∀ n : ℕ,
      (Nat.fib (n + 2) : ℝ) ≤ Real.goldenRatio ^ (n + 1) ∧
        (Nat.fib (n + 3) : ℝ) ≤ Real.goldenRatio ^ (n + 2)
  | 0 => by
      constructor
      · have hphi_ge_one : (1 : ℝ) ≤ Real.goldenRatio := le_of_lt Real.one_lt_goldenRatio
        simpa [Nat.fib] using hphi_ge_one
      · have hphi_sq : (2 : ℝ) ≤ Real.goldenRatio ^ 2 := by
          have hphi_ge_one : (1 : ℝ) ≤ Real.goldenRatio := le_of_lt Real.one_lt_goldenRatio
          nlinarith [Real.goldenRatio_sq, hphi_ge_one]
        simpa [Nat.fib] using hphi_sq
  | n + 1 => by
      rcases conclusion_fiber_multiplicity_diameter_cubedim_rigidity_fib_upper_phi_pow_pair n with
        ⟨hn, hn1⟩
      constructor
      · exact hn1
      · have hfib_nat : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            (Nat.fib_add_two (n := n + 2))
        have hfib :
            (Nat.fib (n + 4) : ℝ) = Nat.fib (n + 2) + Nat.fib (n + 3) := by
          exact_mod_cast hfib_nat
        have hphi_rec :
            Real.goldenRatio ^ (n + 3) =
              Real.goldenRatio ^ (n + 1) + Real.goldenRatio ^ (n + 2) := by
          rw [show n + 3 = (n + 1) + 2 by omega, pow_add, Real.goldenRatio_sq]
          ring
        calc
          (Nat.fib (n + 4) : ℝ) = Nat.fib (n + 2) + Nat.fib (n + 3) := hfib
          _ ≤ Real.goldenRatio ^ (n + 1) + Real.goldenRatio ^ (n + 2) := by gcongr
          _ = Real.goldenRatio ^ (n + 3) := hphi_rec.symm

private lemma conclusion_fiber_multiplicity_diameter_cubedim_rigidity_fib_upper_phi_pow
    (n : ℕ) :
    (Nat.fib (n + 2) : ℝ) ≤ Real.goldenRatio ^ (n + 1) :=
  (conclusion_fiber_multiplicity_diameter_cubedim_rigidity_fib_upper_phi_pow_pair n).1

private lemma conclusion_fiber_multiplicity_diameter_cubedim_rigidity_phi_pow_sum_le_prod :
    ∀ lengths : List ℕ,
      Real.goldenRatio ^ lengths.sum ≤
        conclusion_fiber_multiplicity_diameter_cubedim_rigidity_multiplicity lengths
  | [] => by simp [conclusion_fiber_multiplicity_diameter_cubedim_rigidity_multiplicity]
  | ell :: lengths => by
      have hhead :
          Real.goldenRatio ^ ell ≤ (Nat.fib (ell + 2) : ℝ) :=
        conclusion_fiber_multiplicity_diameter_cubedim_rigidity_fib_lower_phi_pow ell
      have htail :
          Real.goldenRatio ^ lengths.sum ≤
            conclusion_fiber_multiplicity_diameter_cubedim_rigidity_multiplicity lengths :=
        conclusion_fiber_multiplicity_diameter_cubedim_rigidity_phi_pow_sum_le_prod lengths
      calc
        Real.goldenRatio ^ (List.sum (ell :: lengths)) =
            Real.goldenRatio ^ ell * Real.goldenRatio ^ lengths.sum := by
              simp [pow_add]
        _ ≤ (Nat.fib (ell + 2) : ℝ) *
              conclusion_fiber_multiplicity_diameter_cubedim_rigidity_multiplicity lengths := by
              simpa [conclusion_fiber_multiplicity_diameter_cubedim_rigidity_multiplicity] using
                mul_le_mul hhead htail (by positivity) (by positivity)
        _ = conclusion_fiber_multiplicity_diameter_cubedim_rigidity_multiplicity (ell :: lengths) := by
              simp [conclusion_fiber_multiplicity_diameter_cubedim_rigidity_multiplicity]

private lemma conclusion_fiber_multiplicity_diameter_cubedim_rigidity_prod_le_phi_pow_sum_add_length :
    ∀ lengths : List ℕ,
      conclusion_fiber_multiplicity_diameter_cubedim_rigidity_multiplicity lengths ≤
        Real.goldenRatio ^ (lengths.sum + lengths.length)
  | [] => by simp [conclusion_fiber_multiplicity_diameter_cubedim_rigidity_multiplicity]
  | ell :: lengths => by
      have hhead :
          (Nat.fib (ell + 2) : ℝ) ≤ Real.goldenRatio ^ (ell + 1) :=
        conclusion_fiber_multiplicity_diameter_cubedim_rigidity_fib_upper_phi_pow ell
      have htail :
          conclusion_fiber_multiplicity_diameter_cubedim_rigidity_multiplicity lengths ≤
            Real.goldenRatio ^ (lengths.sum + lengths.length) :=
        conclusion_fiber_multiplicity_diameter_cubedim_rigidity_prod_le_phi_pow_sum_add_length lengths
      calc
        conclusion_fiber_multiplicity_diameter_cubedim_rigidity_multiplicity (ell :: lengths) =
            (Nat.fib (ell + 2) : ℝ) *
              conclusion_fiber_multiplicity_diameter_cubedim_rigidity_multiplicity lengths := by
              simp [conclusion_fiber_multiplicity_diameter_cubedim_rigidity_multiplicity]
        _ ≤ Real.goldenRatio ^ (ell + 1) *
              Real.goldenRatio ^ (lengths.sum + lengths.length) := by
              exact mul_le_mul hhead htail
                (show 0 ≤ conclusion_fiber_multiplicity_diameter_cubedim_rigidity_multiplicity lengths by
                  dsimp [conclusion_fiber_multiplicity_diameter_cubedim_rigidity_multiplicity]
                  exact_mod_cast Nat.zero_le ((lengths.map fun ell => Nat.fib (ell + 2)).prod))
                (show 0 ≤ Real.goldenRatio ^ (ell + 1) by positivity)
        _ = Real.goldenRatio ^ ((ell :: lengths).sum + (ell :: lengths).length) := by
              simp [pow_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, mul_assoc, mul_comm,
                mul_left_comm]

private lemma conclusion_fiber_multiplicity_diameter_cubedim_rigidity_sum_le_two_cube :
    ∀ lengths : List ℕ,
      lengths.sum ≤ 2 * Omega.POM.fiberReconstructionCubeDimension lengths
  | [] => by simp [Omega.POM.fiberReconstructionCubeDimension]
  | ell :: lengths => by
      have htail :
          lengths.sum ≤ 2 * Omega.POM.fiberReconstructionCubeDimension lengths :=
        conclusion_fiber_multiplicity_diameter_cubedim_rigidity_sum_le_two_cube lengths
      have hhead : ell ≤ 2 * ((ell + 1) / 2) := by omega
      simp [Omega.POM.fiberReconstructionCubeDimension] at htail ⊢
      omega

private lemma conclusion_fiber_multiplicity_diameter_cubedim_rigidity_two_cube_sub_length_le_sum :
    ∀ lengths : List ℕ,
      2 * Omega.POM.fiberReconstructionCubeDimension lengths - lengths.length ≤ lengths.sum
  | [] => by simp [Omega.POM.fiberReconstructionCubeDimension]
  | ell :: lengths => by
      have htail :
          2 * Omega.POM.fiberReconstructionCubeDimension lengths - lengths.length ≤ lengths.sum :=
        conclusion_fiber_multiplicity_diameter_cubedim_rigidity_two_cube_sub_length_le_sum lengths
      have hhead : 2 * ((ell + 1) / 2) - 1 ≤ ell := by omega
      simp [Omega.POM.fiberReconstructionCubeDimension] at htail ⊢
      omega

/-- Paper label: `thm:conclusion-fiber-multiplicity-diameter-cubedim-rigidity`. The multiplicity
product attached to a path decomposition is squeezed between the diameter and cube-dimension
golden-ratio scales using the standard Fibonacci bounds on each path factor. -/
theorem paper_conclusion_fiber_multiplicity_diameter_cubedim_rigidity (lengths : List ℕ) :
    Real.goldenRatio ^ Omega.POM.fiberReconstructionDiameter lengths ≤
      conclusion_fiber_multiplicity_diameter_cubedim_rigidity_multiplicity lengths ∧
      conclusion_fiber_multiplicity_diameter_cubedim_rigidity_multiplicity lengths ≤
        Real.goldenRatio ^ (Omega.POM.fiberReconstructionDiameter lengths + lengths.length) ∧
      Real.goldenRatio ^
          (2 * Omega.POM.fiberReconstructionCubeDimension lengths - lengths.length) ≤
        conclusion_fiber_multiplicity_diameter_cubedim_rigidity_multiplicity lengths ∧
      conclusion_fiber_multiplicity_diameter_cubedim_rigidity_multiplicity lengths ≤
        Real.goldenRatio ^
          (2 * Omega.POM.fiberReconstructionCubeDimension lengths + lengths.length) := by
  have hcart := Omega.POM.paper_pom_fiber_reconstruction_cartesian_product lengths
  have hdiam :
      Omega.POM.fiberReconstructionDiameter lengths = lengths.sum := hcart.2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hdiam]
    exact conclusion_fiber_multiplicity_diameter_cubedim_rigidity_phi_pow_sum_le_prod lengths
  · rw [hdiam]
    exact conclusion_fiber_multiplicity_diameter_cubedim_rigidity_prod_le_phi_pow_sum_add_length
      lengths
  · have hlower_nat :
        2 * Omega.POM.fiberReconstructionCubeDimension lengths - lengths.length ≤
          Omega.POM.fiberReconstructionDiameter lengths := by
      rw [hdiam]
      exact
        conclusion_fiber_multiplicity_diameter_cubedim_rigidity_two_cube_sub_length_le_sum lengths
    have hmono :
        Real.goldenRatio ^
            (2 * Omega.POM.fiberReconstructionCubeDimension lengths - lengths.length) ≤
          Real.goldenRatio ^ Omega.POM.fiberReconstructionDiameter lengths := by
      exact pow_le_pow_right₀ (le_of_lt Real.one_lt_goldenRatio) hlower_nat
    exact hmono.trans
      (by
        rw [hdiam]
        exact
          conclusion_fiber_multiplicity_diameter_cubedim_rigidity_phi_pow_sum_le_prod lengths)
  · have hupper_nat :
        Omega.POM.fiberReconstructionDiameter lengths + lengths.length ≤
          2 * Omega.POM.fiberReconstructionCubeDimension lengths + lengths.length := by
      have hsum_nat :
          Omega.POM.fiberReconstructionDiameter lengths ≤
            2 * Omega.POM.fiberReconstructionCubeDimension lengths := by
        rw [hdiam]
        exact conclusion_fiber_multiplicity_diameter_cubedim_rigidity_sum_le_two_cube lengths
      omega
    have hmono :
        Real.goldenRatio ^ (Omega.POM.fiberReconstructionDiameter lengths + lengths.length) ≤
          Real.goldenRatio ^
            (2 * Omega.POM.fiberReconstructionCubeDimension lengths + lengths.length) := by
      exact pow_le_pow_right₀ (le_of_lt Real.one_lt_goldenRatio) hupper_nat
    rw [hdiam] at hmono
    exact
      (conclusion_fiber_multiplicity_diameter_cubedim_rigidity_prod_le_phi_pow_sum_add_length
        lengths).trans hmono

end

end Omega.Conclusion
