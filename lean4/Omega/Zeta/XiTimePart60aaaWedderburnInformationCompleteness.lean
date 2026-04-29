import Mathlib.Tactic
import Omega.Conclusion.CapacityFiniteCompleteness
import Omega.Conclusion.CapacityRamanujanPlateauLaw

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete fixed-resolution fiber data. The finite histogram of fiber sizes drives the capacity
curve, moment spectrum, and semisimple block multiplicities. -/
structure xi_time_part60aaa_wedderburn_information_completeness_data where
  xi_time_part60aaa_wedderburn_information_completeness_Fiber : Type
  xi_time_part60aaa_wedderburn_information_completeness_fintype :
    Fintype xi_time_part60aaa_wedderburn_information_completeness_Fiber
  xi_time_part60aaa_wedderburn_information_completeness_size :
    xi_time_part60aaa_wedderburn_information_completeness_Fiber → ℕ

namespace xi_time_part60aaa_wedderburn_information_completeness_data

attribute [instance] xi_time_part60aaa_wedderburn_information_completeness_fintype

/-- The histogram of fiber sizes. -/
def xi_time_part60aaa_wedderburn_information_completeness_histogram
    (D : xi_time_part60aaa_wedderburn_information_completeness_data) (k : ℕ) : ℕ :=
  Fintype.card
    {x : D.xi_time_part60aaa_wedderburn_information_completeness_Fiber //
      D.xi_time_part60aaa_wedderburn_information_completeness_size x = k}

/-- Tail counts of the fiber-size histogram. -/
def xi_time_part60aaa_wedderburn_information_completeness_tailCount
    (D : xi_time_part60aaa_wedderburn_information_completeness_data) (t : ℕ) : ℕ :=
  Fintype.card
    {x : D.xi_time_part60aaa_wedderburn_information_completeness_Fiber //
      t ≤ D.xi_time_part60aaa_wedderburn_information_completeness_size x}

/-- Capacity samples attached to the fiber-size function. -/
def xi_time_part60aaa_wedderburn_information_completeness_capacity
    (D : xi_time_part60aaa_wedderburn_information_completeness_data) (t : ℕ) : ℕ :=
  Omega.Conclusion.CapacityRamanujanPlateauLaw.capacityCurve
    D.xi_time_part60aaa_wedderburn_information_completeness_size t

/-- Positive moment spectrum of the fiber-size histogram. -/
def xi_time_part60aaa_wedderburn_information_completeness_momentSpectrum
    (D : xi_time_part60aaa_wedderburn_information_completeness_data) (q : ℕ) : ℕ :=
  ∑ x : D.xi_time_part60aaa_wedderburn_information_completeness_Fiber,
    D.xi_time_part60aaa_wedderburn_information_completeness_size x ^ q

/-- Semisimple block multiplicities, indexed by matrix block size. -/
def xi_time_part60aaa_wedderburn_information_completeness_semisimpleBlocks
    (D : xi_time_part60aaa_wedderburn_information_completeness_data) : ℕ → ℕ :=
  D.xi_time_part60aaa_wedderburn_information_completeness_histogram

/-- Symmetric-group factors regrouped by equal fiber size. -/
def xi_time_part60aaa_wedderburn_information_completeness_symmetricFactorsBySize
    (D : xi_time_part60aaa_wedderburn_information_completeness_data) : ℕ → ℕ :=
  D.xi_time_part60aaa_wedderburn_information_completeness_histogram

/-- Fixed-resolution information completeness for the histogram, capacity curve, moment spectrum,
semisimple block multiset, and regrouped symmetric-group factors. -/
def xi_time_part60aaa_wedderburn_information_completeness_statement
    (D : xi_time_part60aaa_wedderburn_information_completeness_data) : Prop :=
  Omega.Conclusion.FiniteMultiplicityDataEquivalent
      (X := D.xi_time_part60aaa_wedderburn_information_completeness_Fiber)
      D.xi_time_part60aaa_wedderburn_information_completeness_histogram
      D.xi_time_part60aaa_wedderburn_information_completeness_tailCount
      D.xi_time_part60aaa_wedderburn_information_completeness_capacity
      D.xi_time_part60aaa_wedderburn_information_completeness_momentSpectrum ∧
    D.xi_time_part60aaa_wedderburn_information_completeness_semisimpleBlocks =
      D.xi_time_part60aaa_wedderburn_information_completeness_histogram ∧
    D.xi_time_part60aaa_wedderburn_information_completeness_symmetricFactorsBySize =
      D.xi_time_part60aaa_wedderburn_information_completeness_histogram

end xi_time_part60aaa_wedderburn_information_completeness_data

/-- Paper label: `thm:xi-time-part60aaa-wedderburn-information-completeness`. -/
theorem paper_xi_time_part60aaa_wedderburn_information_completeness
    (D : xi_time_part60aaa_wedderburn_information_completeness_data) :
    D.xi_time_part60aaa_wedderburn_information_completeness_statement := by
  classical
  refine ⟨?_, rfl, rfl⟩
  simpa [
    xi_time_part60aaa_wedderburn_information_completeness_data.xi_time_part60aaa_wedderburn_information_completeness_histogram,
    xi_time_part60aaa_wedderburn_information_completeness_data.xi_time_part60aaa_wedderburn_information_completeness_tailCount,
    xi_time_part60aaa_wedderburn_information_completeness_data.xi_time_part60aaa_wedderburn_information_completeness_capacity,
    xi_time_part60aaa_wedderburn_information_completeness_data.xi_time_part60aaa_wedderburn_information_completeness_momentSpectrum] using
    (Omega.Conclusion.paper_conclusion_capacity_finite_completeness
      (X := D.xi_time_part60aaa_wedderburn_information_completeness_Fiber)
      D.xi_time_part60aaa_wedderburn_information_completeness_size)

end Omega.Zeta
