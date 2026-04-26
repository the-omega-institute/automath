import Mathlib.Tactic

namespace Omega.Conclusion

/-- The Lucas input `L₁ = 1` used in the `m = 6` closed form. -/
def conclusion_window6_fourier_signature_lucas_ramanujan_L1 : ℤ := 1

/-- The Lucas input `L₂ = 3` used in the `m = 6` closed form. -/
def conclusion_window6_fourier_signature_lucas_ramanujan_L2 : ℤ := 3

/-- The Lucas input `L₃ = 4` used in the `m = 6` closed form. -/
def conclusion_window6_fourier_signature_lucas_ramanujan_L3 : ℤ := 4

/-- The Lucas input `L₆ = 18` used in the `m = 6` closed form. -/
def conclusion_window6_fourier_signature_lucas_ramanujan_L6 : ℤ := 18

/-- The elementary Ramanujan sum `c₁(k) = 1`. -/
def conclusion_window6_fourier_signature_lucas_ramanujan_c1 (_k : ℕ) : ℤ := 1

/-- The elementary Ramanujan sum `c₂(k) = (-1)^k`. -/
def conclusion_window6_fourier_signature_lucas_ramanujan_c2 (k : ℕ) : ℤ :=
  if k % 2 = 0 then 1 else -1

/-- The prime Ramanujan sum `c₃(k)`. -/
def conclusion_window6_fourier_signature_lucas_ramanujan_c3 (k : ℕ) : ℤ :=
  if k % 3 = 0 then 2 else -1

/-- The squarefree Ramanujan sum `c₆(k) = 2 cos(πk/3)` on residues modulo `6`. -/
def conclusion_window6_fourier_signature_lucas_ramanujan_c6 (k : ℕ) : ℤ :=
  match k % 6 with
  | 0 => 2
  | 1 => 1
  | 2 => -1
  | 3 => -2
  | 4 => -1
  | _ => 1

/-- The divisor-regrouped multiplicity formula specialized to `m = 6`. -/
def conclusion_window6_fourier_signature_lucas_ramanujan_mult (k : ℕ) : ℤ :=
  (conclusion_window6_fourier_signature_lucas_ramanujan_L1 *
      conclusion_window6_fourier_signature_lucas_ramanujan_c6 k +
    conclusion_window6_fourier_signature_lucas_ramanujan_L2 *
      conclusion_window6_fourier_signature_lucas_ramanujan_c3 k +
    conclusion_window6_fourier_signature_lucas_ramanujan_L3 *
      conclusion_window6_fourier_signature_lucas_ramanujan_c2 k +
    conclusion_window6_fourier_signature_lucas_ramanujan_L6 *
      conclusion_window6_fourier_signature_lucas_ramanujan_c1 k) / 6

/-- Paper label: `cor:conclusion-window6-fourier-signature-lucas-ramanujan`. Instantiating the
Lucas--Ramanujan closed form at `m = 6` yields the six multiplicities `(5, 2, 3, 3, 3, 2)`. -/
theorem paper_conclusion_window6_fourier_signature_lucas_ramanujan :
    conclusion_window6_fourier_signature_lucas_ramanujan_mult 0 = 5 ∧
      conclusion_window6_fourier_signature_lucas_ramanujan_mult 1 = 2 ∧
      conclusion_window6_fourier_signature_lucas_ramanujan_mult 2 = 3 ∧
      conclusion_window6_fourier_signature_lucas_ramanujan_mult 3 = 3 ∧
      conclusion_window6_fourier_signature_lucas_ramanujan_mult 4 = 3 ∧
      conclusion_window6_fourier_signature_lucas_ramanujan_mult 5 = 2 := by
  native_decide

end Omega.Conclusion
