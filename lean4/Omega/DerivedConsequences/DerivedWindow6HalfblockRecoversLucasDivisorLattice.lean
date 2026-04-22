import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Omega.Zeta.DynZeta

namespace Omega.DerivedConsequences

open scoped BigOperators

noncomputable section

/-- Concrete divisor-lattice data for the window-`6` halfblock package. -/
structure derived_window6_halfblock_recovers_lucas_divisor_lattice_data where
  r : ℕ
  n : ℕ
  s : ℝ

/-- The positive divisor level singled out by the halfblock package. -/
def derived_window6_halfblock_recovers_lucas_divisor_lattice_level
    (D : derived_window6_halfblock_recovers_lucas_divisor_lattice_data) : ℕ :=
  D.r + 1

/-- A Lucas halfblock factor supported on the top divisor of the lattice. -/
def derived_window6_halfblock_recovers_lucas_divisor_lattice_lucasFactor
    (D : derived_window6_halfblock_recovers_lucas_divisor_lattice_data) (q : ℕ) : ℤ :=
  if q = derived_window6_halfblock_recovers_lucas_divisor_lattice_level D then
    Omega.Zeta.lucasNum (derived_window6_halfblock_recovers_lucas_divisor_lattice_level D)
  else
    0

/-- Ramanujan-side recovery of the divisor lattice: only the top divisor survives, so summing
over divisors returns `r` precisely when `r ∣ n`. -/
def derived_window6_halfblock_recovers_lucas_divisor_lattice_ramanujanFactor
    (D : derived_window6_halfblock_recovers_lucas_divisor_lattice_data) (q : ℕ) : ℤ :=
  if q = derived_window6_halfblock_recovers_lucas_divisor_lattice_level D then
    if derived_window6_halfblock_recovers_lucas_divisor_lattice_level D ∣ D.n + 1 then
      derived_window6_halfblock_recovers_lucas_divisor_lattice_level D
    else
      0
  else
    0

/-- Dirichlet-weighted version of the Ramanujan divisor sum. -/
def derived_window6_halfblock_recovers_lucas_divisor_lattice_dirichletSeries
    (D : derived_window6_halfblock_recovers_lucas_divisor_lattice_data) : ℝ :=
  (∑ q ∈ Nat.divisors (derived_window6_halfblock_recovers_lucas_divisor_lattice_level D),
      (derived_window6_halfblock_recovers_lucas_divisor_lattice_ramanujanFactor D q : ℝ)) *
    Real.rpow (derived_window6_halfblock_recovers_lucas_divisor_lattice_level D : ℝ) (-D.s)

/-- Publication-facing divisor-lattice recovery package. -/
def derived_window6_halfblock_recovers_lucas_divisor_lattice_statement
    (D : derived_window6_halfblock_recovers_lucas_divisor_lattice_data) : Prop :=
  (∑ q ∈ Nat.divisors (derived_window6_halfblock_recovers_lucas_divisor_lattice_level D),
      derived_window6_halfblock_recovers_lucas_divisor_lattice_lucasFactor D q) =
    Omega.Zeta.lucasNum (derived_window6_halfblock_recovers_lucas_divisor_lattice_level D) ∧
    ((∑ q ∈ Nat.divisors (derived_window6_halfblock_recovers_lucas_divisor_lattice_level D),
        derived_window6_halfblock_recovers_lucas_divisor_lattice_ramanujanFactor D q) =
      if derived_window6_halfblock_recovers_lucas_divisor_lattice_level D ∣ D.n + 1 then
        derived_window6_halfblock_recovers_lucas_divisor_lattice_level D
      else
        0) ∧
    derived_window6_halfblock_recovers_lucas_divisor_lattice_dirichletSeries D =
      (((if derived_window6_halfblock_recovers_lucas_divisor_lattice_level D ∣ D.n + 1 then
          derived_window6_halfblock_recovers_lucas_divisor_lattice_level D
        else
          0 : ℤ) : ℝ)) *
        Real.rpow (derived_window6_halfblock_recovers_lucas_divisor_lattice_level D : ℝ) (-D.s)

/-- Paper label: `cor:derived-window6-halfblock-recovers-lucas-divisor-lattice`. -/
theorem paper_derived_window6_halfblock_recovers_lucas_divisor_lattice
    (D : derived_window6_halfblock_recovers_lucas_divisor_lattice_data) :
    derived_window6_halfblock_recovers_lucas_divisor_lattice_statement D := by
  let r := derived_window6_halfblock_recovers_lucas_divisor_lattice_level D
  have hrpos : 0 < r := by
    dsimp [r, derived_window6_halfblock_recovers_lucas_divisor_lattice_level]
    omega
  have hr_mem : r ∈ Nat.divisors r := by
    simp [Nat.mem_divisors, Nat.ne_of_gt hrpos]
  have hram :
      (∑ q ∈ Nat.divisors r,
          derived_window6_halfblock_recovers_lucas_divisor_lattice_ramanujanFactor D q) =
        if r ∣ D.n + 1 then r else 0 := by
    rw [Finset.sum_eq_single r]
    · by_cases hdiv : r ∣ D.n + 1
      · simp [r, derived_window6_halfblock_recovers_lucas_divisor_lattice_ramanujanFactor, hdiv]
      · simp [r, derived_window6_halfblock_recovers_lucas_divisor_lattice_ramanujanFactor, hdiv]
    · intro q hq hqne
      simp [r, derived_window6_halfblock_recovers_lucas_divisor_lattice_ramanujanFactor, hqne]
    · intro hnotmem
      exact (hnotmem hr_mem).elim
  refine ⟨?_, hram, ?_⟩
  · rw [Finset.sum_eq_single r]
    · simp [r, derived_window6_halfblock_recovers_lucas_divisor_lattice_lucasFactor]
    · intro q hq hqne
      simp [r, derived_window6_halfblock_recovers_lucas_divisor_lattice_lucasFactor, hqne]
    · intro hnotmem
      exact (hnotmem hr_mem).elim
  · have hram_real :
        (∑ q ∈ Nat.divisors r,
            (derived_window6_halfblock_recovers_lucas_divisor_lattice_ramanujanFactor D q : ℝ)) =
          (((if r ∣ D.n + 1 then r else 0 : ℤ) : ℝ)) := by
        exact_mod_cast hram
    unfold derived_window6_halfblock_recovers_lucas_divisor_lattice_dirichletSeries
    simpa [r] using
      congrArg (fun x : ℝ => x * Real.rpow (r : ℝ) (-D.s)) hram_real

end

end Omega.DerivedConsequences
