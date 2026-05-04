import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-laurent-rose-gcd-collapse-index`. -/
theorem paper_conclusion_laurent_rose_gcd_collapse_index (d n : Nat) (hn : 0 < n) :
    (2 * n) / (n / Nat.gcd n d) = 2 * Nat.gcd n d := by
  let g := Nat.gcd n d
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left d hn
  have hgdvd : g ∣ n := Nat.gcd_dvd_left n d
  have hquot_pos : 0 < n / g :=
    Nat.div_pos (Nat.le_of_dvd hn hgdvd) hgpos
  have hmul : (n / g) * g = n := by
    simpa [g] using Nat.div_mul_cancel hgdvd
  have hnum : 2 * n = (n / g) * (2 * g) := by
    nth_rewrite 1 [← hmul]
    ring
  rw [hnum]
  change ((n / g) * (2 * g)) / (n / g) = 2 * g
  exact Nat.mul_div_right (2 * g) hquot_pos

end Omega.Conclusion
