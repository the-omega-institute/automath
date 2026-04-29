import Mathlib.Tactic
import Omega.Folding.FoldBinChi2Col

namespace Omega.Folding

/-- Paper theorem:
`thm:derived-binfold-minsector-chi2-two-block-bound` -/
theorem paper_derived_binfold_minsector_chi2_two_block_bound (m : ℕ) (chi2 delta uSector
    uComplement lowerBound : ℚ) (hm : m = 6 ∨ m = 8 ∨ m = 10 ∨ m = 12)
    (hchi2 : chi2 = Omega.Folding.foldBinChi2Col m)
    (huSector : uSector = (Nat.fib m : ℚ) / Nat.fib (m + 2))
    (huComplement : uComplement = (Nat.fib (m + 1) : ℚ) / Nat.fib (m + 2))
    (hdelta : delta = (Nat.fib m : ℚ) / Nat.fib (m + 2) *
      ((((Nat.fib (m + 2) * Nat.fib (m / 2) : ℕ) : ℚ) / (2 ^ m : ℚ)) - 1))
    (hlower : chi2 ≥ delta ^ 2 / uSector + delta ^ 2 / uComplement)
    (hbound : lowerBound = (Nat.fib m : ℚ) / Nat.fib (m + 1) *
      (((((Nat.fib (m + 2) * Nat.fib (m / 2) : ℕ) : ℚ) / (2 ^ m : ℚ)) - 1) ^ 2)) :
    chi2 ≥ lowerBound := by
  have hm_pos : 0 < m := by
    rcases hm with rfl | rfl | rfl | rfl <;> decide
  have hfibm_ne : (Nat.fib m : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.fib_pos.mpr hm_pos)
  have hfibm1_ne : (Nat.fib (m + 1) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.fib_pos.mpr (Nat.succ_pos _))
  have hfibm2_ne : (Nat.fib (m + 2) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.fib_pos.mpr (by omega))
  have hfib_add : (Nat.fib (m + 2) : ℚ) = Nat.fib m + Nat.fib (m + 1) := by
    exact_mod_cast (Nat.fib_add_two (n := m))
  subst chi2
  subst uSector
  subst uComplement
  subst delta
  subst lowerBound
  set t : ℚ :=
    (((Nat.fib (m + 2) * Nat.fib (m / 2) : ℕ) : ℚ) / (2 ^ m : ℚ)) - 1
  have hsector_ne : ((Nat.fib m : ℚ) / Nat.fib (m + 2)) ≠ 0 := by
    exact div_ne_zero hfibm_ne hfibm2_ne
  have hcomplement_ne : ((Nat.fib (m + 1) : ℚ) / Nat.fib (m + 2)) ≠ 0 := by
    exact div_ne_zero hfibm1_ne hfibm2_ne
  have hrewrite :
      (((Nat.fib m : ℚ) / Nat.fib (m + 2) * t) ^ 2 / ((Nat.fib m : ℚ) / Nat.fib (m + 2)) +
        ((Nat.fib m : ℚ) / Nat.fib (m + 2) * t) ^ 2 / ((Nat.fib (m + 1) : ℚ) / Nat.fib (m + 2))) =
        (Nat.fib m : ℚ) / Nat.fib (m + 1) * t ^ 2 := by
    have hfib_add' : (Nat.fib (m + 1) : ℚ) + Nat.fib m = Nat.fib (m + 2) := by
      simpa [add_comm] using hfib_add.symm
    have hmultip :
        t ^ 2 * ((Nat.fib (m + 1) : ℚ) + Nat.fib m) = t ^ 2 * Nat.fib (m + 2) := by
      exact congrArg (fun z : ℚ => t ^ 2 * z) hfib_add'
    field_simp [hsector_ne, hcomplement_ne, hfibm_ne, hfibm1_ne, hfibm2_ne]
    ring_nf
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, left_distrib, add_comm, add_left_comm,
      add_assoc] using hmultip
  calc
    Omega.Folding.foldBinChi2Col m ≥
        (((Nat.fib m : ℚ) / Nat.fib (m + 2) * t) ^ 2 / ((Nat.fib m : ℚ) / Nat.fib (m + 2)) +
          ((Nat.fib m : ℚ) / Nat.fib (m + 2) * t) ^ 2 / ((Nat.fib (m + 1) : ℚ) / Nat.fib (m + 2))) := by
          simpa [t] using hlower
    _ = (Nat.fib m : ℚ) / Nat.fib (m + 1) * t ^ 2 := hrewrite
    _ = (Nat.fib m : ℚ) / Nat.fib (m + 1) *
          (((((Nat.fib (m + 2) * Nat.fib (m / 2) : ℕ) : ℚ) / (2 ^ m : ℚ)) - 1) ^ 2) := by
          simp [t]

end Omega.Folding
