import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-family-number-window-quantization-minimal-window`. -/
theorem paper_xi_family_number_window_quantization_minimal_window
    (m Nf boundary : ℕ) (hm : 6 ≤ m) (hEq : 15 * Nf + boundary = 16 * Nf)
    (hBoundary : boundary = Nat.fib (m - 2)) (hNf : Nf = 3) :
    Nf = Nat.fib (m - 2) ∧ m = 6 := by
  have hboundary_eq_Nf : boundary = Nf := by omega
  have hfib : Nat.fib (m - 2) = Nat.fib 4 := by
    rw [← hBoundary, hboundary_eq_Nf, hNf]
    norm_num [Nat.fib]
  have hm_sub_ge : 4 ≤ m - 2 := by omega
  have hm_sub_le : m - 2 ≤ 4 := by
    by_contra hle
    have hlt : 4 < m - 2 := Nat.lt_of_not_ge hle
    have hstrict : Nat.fib 4 < Nat.fib (m - 2) :=
      (Nat.fib_lt_fib (by decide : 2 ≤ 4)).2 hlt
    exact (lt_irrefl (Nat.fib 4)) (hfib.symm ▸ hstrict)
  have hm_eq : m = 6 := by omega
  constructor
  · rw [hNf, hm_eq]
    norm_num [Nat.fib]
  · exact hm_eq

end Omega.Zeta
