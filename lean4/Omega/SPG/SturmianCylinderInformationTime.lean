import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Core.Fib

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Continued-fraction cylinder bounds give a logarithmic sandwich for the information time.
    thm:spg-sturmian-cylinder-measure-continued-fraction-sandwich -/
theorem paper_spg_sturmian_cylinder_measure_continued_fraction_sandwich
    (q : ℕ → ℕ) (cyl : ℕ → ℝ) (N : ℕ → ℕ) (hq : ∀ n, 1 ≤ q n)
    (hIndex : ∀ t ≥ 1, q (N t) ≤ t ∧ t < q (N t + 1))
    (hCyl : ∀ t ≥ 1,
      (1 : ℝ) / ((q (N t + 1) + q (N t) : ℕ) : ℝ) < cyl t ∧
        cyl t < (1 : ℝ) / (q (N t) : ℝ) + (1 : ℝ) / (q (N t + 1) : ℝ)) :
    ∀ t ≥ 1,
      Real.log ((q (N t) : ℝ) / 2) < -Real.log (cyl t) ∧
        -Real.log (cyl t) < Real.log ((q (N t + 1) + q (N t) : ℕ) : ℝ) := by
  intro t ht
  rcases hIndex t ht with ⟨hqt, htq⟩
  rcases hCyl t ht with ⟨hCylLower, hCylUpper⟩
  have hqPosNat : 0 < q (N t) := by
    have : 1 ≤ q (N t) := hq (N t)
    omega
  have hSumPosNat : 0 < q (N t + 1) + q (N t) := by
    have : 1 ≤ q (N t + 1) := hq (N t + 1)
    omega
  have hqPos : 0 < (q (N t) : ℝ) := by
    exact_mod_cast hqPosNat
  have hSumPos : 0 < ((q (N t + 1) + q (N t) : ℕ) : ℝ) := by
    exact_mod_cast hSumPosNat
  have hCylPos : 0 < cyl t := by
    exact lt_trans (one_div_pos.mpr hSumPos) hCylLower
  have hqLtNat : q (N t) < q (N t + 1) := by
    exact lt_of_le_of_lt hqt htq
  have hqLt : (q (N t) : ℝ) < (q (N t + 1) : ℝ) := by
    exact_mod_cast hqLtNat
  have hInvLt : (1 : ℝ) / (q (N t + 1) : ℝ) < (1 : ℝ) / (q (N t) : ℝ) := by
    exact one_div_lt_one_div_of_lt hqPos hqLt
  have hUpperTwo : cyl t < (2 : ℝ) / (q (N t) : ℝ) := by
    calc
      cyl t < (1 : ℝ) / (q (N t) : ℝ) + (1 : ℝ) / (q (N t + 1) : ℝ) := hCylUpper
      _ < (1 : ℝ) / (q (N t) : ℝ) + (1 : ℝ) / (q (N t) : ℝ) := by
        linarith
      _ = (2 : ℝ) / (q (N t) : ℝ) := by
        ring
  have hLogUpper : Real.log (cyl t) < Real.log ((2 : ℝ) / (q (N t) : ℝ)) := by
    exact Real.log_lt_log hCylPos hUpperTwo
  have hLogUpperEq : Real.log ((2 : ℝ) / (q (N t) : ℝ)) = -Real.log ((q (N t) : ℝ) / 2) := by
    have hInvEq : ((q (N t) : ℝ) / 2)⁻¹ = (2 : ℝ) / (q (N t) : ℝ) := by
      field_simp [hqPos.ne']
    rw [← hInvEq]
    exact Real.log_inv _
  have hLowerInv : (((q (N t + 1) + q (N t) : ℕ) : ℝ)⁻¹) < cyl t := by
    simpa [one_div] using hCylLower
  have hLogLower : Real.log (((q (N t + 1) + q (N t) : ℕ) : ℝ)⁻¹) < Real.log (cyl t) := by
    have hLeftPos : 0 < (((q (N t + 1) + q (N t) : ℕ) : ℝ)⁻¹) := by
      positivity
    exact Real.log_lt_log hLeftPos hLowerInv
  have hLogLowerEq :
      Real.log (((q (N t + 1) + q (N t) : ℕ) : ℝ)⁻¹) =
        -Real.log (((q (N t + 1) + q (N t) : ℕ) : ℝ)) := by
    exact Real.log_inv _
  constructor
  · linarith
  · linarith

set_option maxHeartbeats 400000 in
/-- Golden-slope specialization of the continued-fraction cylinder sandwich: the convergent
denominators are Fibonacci numbers, so the logarithmic information time bounds become rigid
Fibonacci bounds.
    cor:spg-golden-sturmian-log-information-time-rigid -/
theorem paper_spg_golden_sturmian_log_information_time_rigid
    (cyl : Nat -> Real) (N : Nat -> Nat)
    (hIndex : forall t, 1 <= t -> Nat.fib (N t + 1) <= t /\ t < Nat.fib (N t + 2))
    (hCyl : forall t, 1 <= t ->
      (1 : Real) / (((Nat.fib (N t + 2) + Nat.fib (N t + 1) : Nat) : Real)) < cyl t /\
        cyl t < (1 : Real) / ((Nat.fib (N t + 1) : Nat) : Real) +
          (1 : Real) / ((Nat.fib (N t + 2) : Nat) : Real)) :
    forall t, 1 <= t ->
      Real.log (((Nat.fib (N t + 1) : Nat) : Real) / 2) < -Real.log (cyl t) /\
        -Real.log (cyl t) < Real.log (((Nat.fib (N t + 2) + Nat.fib (N t + 1) : Nat) : Real)) := by
  simpa using
    paper_spg_sturmian_cylinder_measure_continued_fraction_sandwich
      (q := fun n => Nat.fib (n + 1))
      (cyl := cyl)
      (N := N)
      (hq := Omega.one_le_fib_succ)
      (hIndex := hIndex)
      (hCyl := hCyl)

end Omega.SPG
