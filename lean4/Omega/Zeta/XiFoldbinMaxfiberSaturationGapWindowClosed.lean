import Mathlib.Tactic
import Omega.Folding.FoldBinDigitDP

namespace Omega.Zeta

private lemma xi_foldbin_maxfiber_saturation_gap_window_closed_sum_odd_step
    (a n : ℕ) :
    (Finset.range n).sum (fun i => Nat.fib (a + 1 + 2 * i)) =
      Nat.fib (a + 2 * n) - Nat.fib a := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hrec :
          Nat.fib (a + 2 * (n + 1)) =
            Nat.fib (a + 2 * n) + Nat.fib (a + 1 + 2 * n) := by
        simpa [Nat.mul_succ, two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          using Nat.fib_add_two (n := a + 2 * n)
      have hle : Nat.fib a ≤ Nat.fib (a + 2 * n) := Nat.fib_mono (by omega)
      omega

private lemma xi_foldbin_maxfiber_saturation_gap_window_closed_even (r : ℕ) :
    (Finset.range (((2 * r) + 1) / 2)).sum
        (fun j => Nat.fib ((2 * r + 2 * r) + 1 - 2 * j)) =
      Nat.fib ((2 * r + 2 * r) + 2) - Nat.fib (2 * r + 1 + 1) := by
  have hcard : ((2 * r + 1) / 2) = r := by omega
  rw [hcard]
  have hreflect := Finset.sum_range_reflect
    (fun i => Nat.fib (2 * r + 3 + 2 * i)) r
  calc
    (Finset.range r).sum (fun j => Nat.fib (2 * r + 2 * r + 1 - 2 * j))
        = (Finset.range r).sum (fun j => Nat.fib (2 * r + 3 + 2 * (r - 1 - j))) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          have hjlt : j < r := Finset.mem_range.mp hj
          congr 1
          omega
    _ = (Finset.range r).sum (fun i => Nat.fib (2 * r + 3 + 2 * i)) := hreflect
    _ = Nat.fib (2 * r + 2 * r + 2) - Nat.fib (2 * r + 1 + 1) := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, two_mul]
            using xi_foldbin_maxfiber_saturation_gap_window_closed_sum_odd_step
              (a := 2 * r + 2) (n := r)

private lemma xi_foldbin_maxfiber_saturation_gap_window_closed_odd (r : ℕ) :
    (Finset.range (((2 * r + 1) + 1) / 2)).sum
        (fun j => Nat.fib (((2 * r + 1) + (2 * r + 1)) + 1 - 2 * j)) =
      Nat.fib (((2 * r + 1) + (2 * r + 1)) + 2) - Nat.fib (2 * r + 1 + 1) := by
  have hcard : ((2 * r + 1 + 1) / 2) = r + 1 := by omega
  rw [hcard]
  have hreflect := Finset.sum_range_reflect
    (fun i => Nat.fib (2 * r + 3 + 2 * i)) (r + 1)
  calc
    (Finset.range (r + 1)).sum
        (fun j => Nat.fib (2 * r + 1 + (2 * r + 1) + 1 - 2 * j))
        = (Finset.range (r + 1)).sum
            (fun j => Nat.fib (2 * r + 3 + 2 * (r + 1 - 1 - j))) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          have hjlt : j < r + 1 := Finset.mem_range.mp hj
          congr 1
          omega
    _ = (Finset.range (r + 1)).sum (fun i => Nat.fib (2 * r + 3 + 2 * i)) :=
          hreflect
    _ = Nat.fib (2 * r + 1 + (2 * r + 1) + 2) - Nat.fib (2 * r + 1 + 1) := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, two_mul]
            using xi_foldbin_maxfiber_saturation_gap_window_closed_sum_odd_step
              (a := 2 * r + 2) (n := r + 1)

/-- Paper label: `thm:xi-foldbin-maxfiber-saturation-gap-window-closed`. -/
theorem paper_xi_foldbin_maxfiber_saturation_gap_window_closed (m : ℕ) :
    let L := Omega.Folding.foldBinDigitTailLength m
    let K := m + L
    let eps := if L % 2 = 0 then 1 else 0
    (Finset.range ((L + 1) / 2)).sum (fun j => Nat.fib (K + 1 - 2 * j)) =
      Nat.fib (K + 2) - Nat.fib (m + 1 + eps) := by
  rw [Omega.Folding.foldBinDigitTailLength_eq]
  by_cases hm : m % 2 = 0
  · obtain ⟨r, rfl⟩ := Nat.even_iff.mpr hm
    have hmod : (r + r) % 2 = 0 := Nat.even_iff.mp ⟨r, rfl⟩
    simpa [hmod, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, two_mul]
      using xi_foldbin_maxfiber_saturation_gap_window_closed_even r
  · have hodd : m % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one m with hzero | hone
      · exact (hm hzero).elim
      · exact hone
    obtain ⟨r, rfl⟩ := Nat.odd_iff.mpr hodd
    have hmod : (2 * r + 1) % 2 = 1 := Nat.odd_iff.mp ⟨r, rfl⟩
    have hmod' : (r + (r + 1)) % 2 = 1 := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, two_mul] using hmod
    simpa [hmod, hmod', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, two_mul]
      using xi_foldbin_maxfiber_saturation_gap_window_closed_odd r

end Omega.Zeta
