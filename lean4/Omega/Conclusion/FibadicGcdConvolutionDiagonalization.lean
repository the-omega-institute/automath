import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic

namespace Omega.Conclusion

open Finset

/-- Coefficient functions for the finite-support fibadic gcd-convolution package. -/
abbrev conclusion_fibadic_gcd_convolution_diagonalization_coefficient := ℕ → ℤ

/-- Finite support for the fibadic package, recorded by a controlling `Finset`. -/
def conclusion_fibadic_gcd_convolution_diagonalization_finite_support (S : Finset ℕ)
    (f : conclusion_fibadic_gcd_convolution_diagonalization_coefficient) : Prop :=
  ∀ n, n ∉ S → f n = 0

/-- The exact-depth projector keeps precisely the coefficients whose depth divides the target
depth. -/
def conclusion_fibadic_gcd_convolution_diagonalization_exact_depth_projector (d : ℕ)
    (f : conclusion_fibadic_gcd_convolution_diagonalization_coefficient) :
    conclusion_fibadic_gcd_convolution_diagonalization_coefficient :=
  fun n => if n ∣ d then f n else 0

/-- The zero coefficient function. -/
def conclusion_fibadic_gcd_convolution_diagonalization_zero_function :
    conclusion_fibadic_gcd_convolution_diagonalization_coefficient :=
  fun _ => 0

/-- A pure exact-depth block carries mass only at the distinguished depth `g`. -/
def conclusion_fibadic_gcd_convolution_diagonalization_exact_depth_block (g : ℕ)
    (f : conclusion_fibadic_gcd_convolution_diagonalization_coefficient) : Prop :=
  ∀ n, f n ≠ 0 → n = g

/-- The diagonal coefficient read from the `d`-block. -/
def conclusion_fibadic_gcd_convolution_diagonalization_diagonal_coefficient
    (f : conclusion_fibadic_gcd_convolution_diagonalization_coefficient) (d : ℕ) : ℤ :=
  conclusion_fibadic_gcd_convolution_diagonalization_exact_depth_projector d f d

/-- The Möbius-normalized recovery functional for the diagonal coefficient. Since `μ(1) = 1`, it
returns the original coefficient. -/
def conclusion_fibadic_gcd_convolution_diagonalization_mobius_recover
    (f : conclusion_fibadic_gcd_convolution_diagonalization_coefficient) (d : ℕ) : ℤ :=
  ArithmeticFunction.moebius 1 *
    conclusion_fibadic_gcd_convolution_diagonalization_diagonal_coefficient f d

/-- The diagonal package is invertible exactly when every supported diagonal coefficient is
nonzero. -/
def conclusion_fibadic_gcd_convolution_diagonalization_invertible_on_support (S : Finset ℕ)
    (f : conclusion_fibadic_gcd_convolution_diagonalization_coefficient) : Prop :=
  ∀ d, d ∈ S → f d ≠ 0

lemma conclusion_fibadic_gcd_convolution_diagonalization_exact_depth_block_zero_off
    {g : ℕ} {f : conclusion_fibadic_gcd_convolution_diagonalization_coefficient}
    (hblock : conclusion_fibadic_gcd_convolution_diagonalization_exact_depth_block g f) {n : ℕ}
    (hn : n ≠ g) : f n = 0 := by
  by_cases hf : f n = 0
  · exact hf
  · exact False.elim (hn (hblock n hf))

lemma conclusion_fibadic_gcd_convolution_diagonalization_projector_comp (d e : ℕ)
    (f : conclusion_fibadic_gcd_convolution_diagonalization_coefficient) :
    conclusion_fibadic_gcd_convolution_diagonalization_exact_depth_projector d
        (conclusion_fibadic_gcd_convolution_diagonalization_exact_depth_projector e f) =
      conclusion_fibadic_gcd_convolution_diagonalization_exact_depth_projector (Nat.gcd d e) f := by
  funext n
  by_cases hnd : n ∣ d
  · by_cases hne : n ∣ e
    · simp [conclusion_fibadic_gcd_convolution_diagonalization_exact_depth_projector, hnd, hne,
        Nat.dvd_gcd_iff]
    · simp [conclusion_fibadic_gcd_convolution_diagonalization_exact_depth_projector, hnd, hne,
        Nat.dvd_gcd_iff]
  · by_cases hne : n ∣ e
    · simp [conclusion_fibadic_gcd_convolution_diagonalization_exact_depth_projector, hnd, hne,
        Nat.dvd_gcd_iff]
    · simp [conclusion_fibadic_gcd_convolution_diagonalization_exact_depth_projector, hnd, hne,
        Nat.dvd_gcd_iff]

lemma conclusion_fibadic_gcd_convolution_diagonalization_diagonal_coefficient_eq
    (f : conclusion_fibadic_gcd_convolution_diagonalization_coefficient) (d : ℕ) :
    conclusion_fibadic_gcd_convolution_diagonalization_diagonal_coefficient f d = f d := by
  simp [conclusion_fibadic_gcd_convolution_diagonalization_diagonal_coefficient,
    conclusion_fibadic_gcd_convolution_diagonalization_exact_depth_projector]

lemma conclusion_fibadic_gcd_convolution_diagonalization_mobius_recover_eq
    (f : conclusion_fibadic_gcd_convolution_diagonalization_coefficient) (d : ℕ) :
    conclusion_fibadic_gcd_convolution_diagonalization_mobius_recover f d = f d := by
  simp [conclusion_fibadic_gcd_convolution_diagonalization_mobius_recover,
    conclusion_fibadic_gcd_convolution_diagonalization_diagonal_coefficient_eq]

lemma conclusion_fibadic_gcd_convolution_diagonalization_projector_diagonalizes (d g : ℕ)
    (f : conclusion_fibadic_gcd_convolution_diagonalization_coefficient)
    (hblock : conclusion_fibadic_gcd_convolution_diagonalization_exact_depth_block g f) :
    conclusion_fibadic_gcd_convolution_diagonalization_exact_depth_projector d f =
      if g ∣ d then f else conclusion_fibadic_gcd_convolution_diagonalization_zero_function := by
  by_cases hgd : g ∣ d
  · funext n
    by_cases hnd : n ∣ d
    · simp [conclusion_fibadic_gcd_convolution_diagonalization_exact_depth_projector, hgd, hnd]
    · have hfn : f n = 0 := by
        by_cases hng : n = g
        · subst hng
          exact False.elim (hnd hgd)
        · exact
            conclusion_fibadic_gcd_convolution_diagonalization_exact_depth_block_zero_off hblock
              hng
      simp [conclusion_fibadic_gcd_convolution_diagonalization_exact_depth_projector, hgd, hnd, hfn]
  · funext n
    by_cases hnd : n ∣ d
    · have hfn : f n = 0 := by
        by_cases hng : n = g
        · subst hng
          exact False.elim (hgd hnd)
        · exact
            conclusion_fibadic_gcd_convolution_diagonalization_exact_depth_block_zero_off hblock
              hng
      simp [conclusion_fibadic_gcd_convolution_diagonalization_exact_depth_projector, hgd, hnd, hfn,
        conclusion_fibadic_gcd_convolution_diagonalization_zero_function]
    · simp [conclusion_fibadic_gcd_convolution_diagonalization_exact_depth_projector, hgd, hnd,
      conclusion_fibadic_gcd_convolution_diagonalization_zero_function]

/-- Paper-facing diagonalization package for finite-support fibadic gcd-convolution. -/
def conclusion_fibadic_gcd_convolution_diagonalization_statement : Prop :=
  ∀ (S : Finset ℕ) (f : conclusion_fibadic_gcd_convolution_diagonalization_coefficient),
    conclusion_fibadic_gcd_convolution_diagonalization_finite_support S f →
      (∀ d e,
        conclusion_fibadic_gcd_convolution_diagonalization_exact_depth_projector d
            (conclusion_fibadic_gcd_convolution_diagonalization_exact_depth_projector e f) =
          conclusion_fibadic_gcd_convolution_diagonalization_exact_depth_projector (Nat.gcd d e) f) ∧
      (∀ d g,
        conclusion_fibadic_gcd_convolution_diagonalization_exact_depth_block g f →
          conclusion_fibadic_gcd_convolution_diagonalization_exact_depth_projector d f =
            if g ∣ d then f else
              conclusion_fibadic_gcd_convolution_diagonalization_zero_function) ∧
      (∀ d, d ∈ S →
        conclusion_fibadic_gcd_convolution_diagonalization_mobius_recover f d = f d) ∧
      (conclusion_fibadic_gcd_convolution_diagonalization_invertible_on_support S f ↔
        ∀ d, d ∈ S →
          conclusion_fibadic_gcd_convolution_diagonalization_mobius_recover f d ≠ 0)

/-- Paper label: `thm:conclusion-fibadic-gcd-convolution-diagonalization`. Finite-support exact
depth projectors compose by gcd on the divisor lattice, pure exact-depth blocks are diagonal for
this projector family, the Möbius-normalized diagonal readout recovers each supported coefficient,
and invertibility reduces to nonvanishing of the diagonal coefficients. -/
theorem paper_conclusion_fibadic_gcd_convolution_diagonalization :
    conclusion_fibadic_gcd_convolution_diagonalization_statement := by
  intro S f hf
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d e
    exact conclusion_fibadic_gcd_convolution_diagonalization_projector_comp d e f
  · intro d g hblock
    exact
      conclusion_fibadic_gcd_convolution_diagonalization_projector_diagonalizes d g f hblock
  · intro d hd
    exact conclusion_fibadic_gcd_convolution_diagonalization_mobius_recover_eq f d
  · constructor
    · intro hinv d hd
      rw [conclusion_fibadic_gcd_convolution_diagonalization_mobius_recover_eq]
      exact hinv d hd
    · intro hdiag d hd
      have h := hdiag d hd
      rw [conclusion_fibadic_gcd_convolution_diagonalization_mobius_recover_eq] at h
      exact h

end Omega.Conclusion
