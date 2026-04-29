import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic

namespace Omega.Zeta

open Polynomial IsFractionRing

lemma xi_terminal_zm_stokes_amplitude_square_cubic_rigidity_three_dvd_den
    (n d : ℤ)
    (h :
      (162 : ℤ) * n ^ 3 + 1593 * n ^ 2 * d + 1998 * n * d ^ 2 + 1184 * d ^ 3 =
        0) :
    (3 : ℤ) ∣ d := by
  have hh := congrArg (fun z : ℤ => (z : ZMod 3)) h
  simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_zero] at hh
  have c162 : (162 : ZMod 3) = 0 := by decide
  have c1593 : (1593 : ZMod 3) = 0 := by decide
  have c1998 : (1998 : ZMod 3) = 0 := by decide
  have c1184 : (1184 : ZMod 3) = 2 := by decide
  rw [c162, c1593, c1998, c1184] at hh
  norm_num at hh
  rcases hh with hbad | hd
  · exact False.elim ((by decide : ¬ (2 : ZMod 3) = 0) hbad)
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd d 3).mp hd

lemma xi_terminal_zm_stokes_amplitude_square_cubic_rigidity_nine_dvd_den
    (n d : ℤ)
    (h :
      (162 : ℤ) * n ^ 3 + 1593 * n ^ 2 * d + 1998 * n * d ^ 2 + 1184 * d ^ 3 =
        0)
    (h3d : (3 : ℤ) ∣ d) :
    (9 : ℤ) ∣ d := by
  obtain ⟨e, rfl⟩ := h3d
  have hq :
      (6 : ℤ) * n ^ 3 + 177 * n ^ 2 * e + 666 * n * e ^ 2 + 1184 * e ^ 3 =
        0 := by
    nlinarith
  have hh := congrArg (fun z : ℤ => (z : ZMod 3)) hq
  simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_zero] at hh
  have c6 : (6 : ZMod 3) = 0 := by decide
  have c177 : (177 : ZMod 3) = 0 := by decide
  have c666 : (666 : ZMod 3) = 0 := by decide
  have c1184 : (1184 : ZMod 3) = 2 := by decide
  rw [c6, c177, c666, c1184] at hh
  norm_num at hh
  have h3e : (3 : ℤ) ∣ e := by
    rcases hh with hbad | he
    · exact False.elim ((by decide : ¬ (2 : ZMod 3) = 0) hbad)
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd e 3).mp he
  obtain ⟨k, rfl⟩ := h3e
  use k
  ring

lemma xi_terminal_zm_stokes_amplitude_square_cubic_rigidity_three_dvd_num
    (n d : ℤ)
    (h :
      (162 : ℤ) * n ^ 3 + 1593 * n ^ 2 * d + 1998 * n * d ^ 2 + 1184 * d ^ 3 =
        0)
    (h9d : (9 : ℤ) ∣ d) :
    (3 : ℤ) ∣ n := by
  obtain ⟨e, rfl⟩ := h9d
  have hq :
      (2 : ℤ) * n ^ 3 + 177 * n ^ 2 * e + 1998 * n * e ^ 2 + 10656 * e ^ 3 =
        0 := by
    nlinarith
  have hh := congrArg (fun z : ℤ => (z : ZMod 3)) hq
  simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_zero] at hh
  have c2 : (2 : ZMod 3) = 2 := by decide
  have c177 : (177 : ZMod 3) = 0 := by decide
  have c1998 : (1998 : ZMod 3) = 0 := by decide
  have c10656 : (10656 : ZMod 3) = 0 := by decide
  rw [c2, c177, c1998, c10656] at hh
  norm_num at hh
  rcases hh with hbad | hn
  · exact False.elim ((by decide : ¬ (2 : ZMod 3) = 0) hbad)
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd n 3).mp hn

lemma xi_terminal_zm_stokes_amplitude_square_cubic_rigidity_no_rational_root
    (q : ℚ) :
    (162 : ℚ) * q ^ 3 + 1593 * q ^ 2 + 1998 * q + 1184 ≠ 0 := by
  intro h
  let f : ℤ[X] :=
    C (162 : ℤ) * X ^ 3 + C (1593 : ℤ) * X ^ 2 + C (1998 : ℤ) * X + C (1184 : ℤ)
  have hf : aeval q f = 0 := by
    dsimp [f]
    simp only [map_add, map_mul, map_pow, aeval_X, aeval_C]
    norm_num
    ring_nf at h ⊢
    exact h
  let n : ℤ := IsFractionRing.num ℤ q
  let d : ℤ := (IsFractionRing.den ℤ q : ℤ)
  have hd0 : (d : ℚ) ≠ 0 := by
    have hdZ : d ≠ 0 := by
      dsimp [d]
      exact mem_nonZeroDivisors_iff_ne_zero.mp (IsFractionRing.den ℤ q).2
    exact_mod_cast hdZ
  have hq : q = (n : ℚ) / (d : ℚ) :=
    (IsFractionRing.mk'_num_den' ℤ q).symm
  have hscaled :
      (162 : ℤ) * n ^ 3 + 1593 * n ^ 2 * d + 1998 * n * d ^ 2 + 1184 * d ^ 3 =
        0 := by
    have h' := h
    rw [hq] at h'
    field_simp [hd0] at h'
    ring_nf at h' ⊢
    exact_mod_cast h'
  have h3d :
      (3 : ℤ) ∣ d :=
    xi_terminal_zm_stokes_amplitude_square_cubic_rigidity_three_dvd_den n d hscaled
  have h9d :
      (9 : ℤ) ∣ d :=
    xi_terminal_zm_stokes_amplitude_square_cubic_rigidity_nine_dvd_den n d hscaled h3d
  have h3n :
      (3 : ℤ) ∣ n :=
    xi_terminal_zm_stokes_amplitude_square_cubic_rigidity_three_dvd_num n d hscaled h9d
  have hrel : IsRelPrime n d := by
    dsimp [n, d]
    exact IsFractionRing.num_den_reduced ℤ q
  have hunit : IsUnit (3 : ℤ) :=
    (hrel.of_dvd_left h3n).isUnit_of_dvd h3d
  norm_num [Int.isUnit_iff] at hunit

/-- Paper label: `thm:xi-terminal-zm-stokes-amplitude-square-cubic-rigidity`. -/
theorem paper_xi_terminal_zm_stokes_amplitude_square_cubic_rigidity :
    (∀ q : ℚ, (162 : ℚ) * q ^ 3 + 1593 * q ^ 2 + 1998 * q + 1184 ≠ 0) ∧
      (let disc : ℤ :=
        1593 ^ 2 * 1998 ^ 2 - 4 * 162 * 1998 ^ 3 - 4 * 1593 ^ 3 * 1184 -
          27 * 162 ^ 2 * 1184 ^ 2 + 18 * 162 * 1593 * 1998 * 1184;
        disc = -2 ^ 2 * 3 ^ 9 * 11 ^ 2 * 37 * 109 ^ 2 ∧ disc < 0) := by
  refine ⟨xi_terminal_zm_stokes_amplitude_square_cubic_rigidity_no_rational_root, ?_⟩
  norm_num

end Omega.Zeta
