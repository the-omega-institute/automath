import Mathlib.Tactic
import Omega.Conclusion.FibadicGcdConvolutionDiagonalization
import Omega.Conclusion.FibadicVisibleDepthMobiusCount

namespace Omega.Conclusion

abbrev conclusion_fibadic_visible_depth_mobius_primitive_semisimplicity_coefficient :=
  conclusion_fibadic_gcd_convolution_diagonalization_coefficient

/-- The pointwise semisimple model records the exact-depth packet on the divisor support of `d`. -/
noncomputable def conclusion_fibadic_visible_depth_mobius_primitive_semisimplicity_semisimple_model
    (d : ℕ) :
    conclusion_fibadic_visible_depth_mobius_primitive_semisimplicity_coefficient :=
  fun n =>
    if n ∈ Nat.divisors d then conclusion_fibadic_visible_depth_mobius_count_exact_count n else 0

/-- Conclusion-level package for the divisor-sum identity and the finite-support diagonal model of
the fibadic Möbius packet. -/
def conclusion_fibadic_visible_depth_mobius_primitive_semisimplicity_statement : Prop :=
  ∀ d : ℕ,
    conclusion_fibadic_visible_depth_mobius_count_exact_count d =
      ∑ e ∈ Nat.divisors d,
        ArithmeticFunction.moebius e *
          conclusion_fibadic_visible_depth_mobius_count_visible_count (d / e) ∧
    conclusion_fibadic_visible_depth_mobius_count_visible_total_from_exact d =
      ∑ e ∈ Nat.divisors d, conclusion_fibadic_visible_depth_mobius_count_exact_count e ∧
    conclusion_fibadic_gcd_convolution_diagonalization_finite_support (Nat.divisors d)
      (conclusion_fibadic_visible_depth_mobius_primitive_semisimplicity_semisimple_model d) ∧
    (∀ m n, n ∈ Nat.divisors d →
      conclusion_fibadic_gcd_convolution_diagonalization_exact_depth_projector m
          (conclusion_fibadic_visible_depth_mobius_primitive_semisimplicity_semisimple_model d) n =
        if n ∣ m then conclusion_fibadic_visible_depth_mobius_count_exact_count n else 0) ∧
    (∀ n, n ∈ Nat.divisors d →
      conclusion_fibadic_gcd_convolution_diagonalization_diagonal_coefficient
          (conclusion_fibadic_visible_depth_mobius_primitive_semisimplicity_semisimple_model d) n =
        conclusion_fibadic_visible_depth_mobius_count_exact_count n) ∧
    (∀ n, n ∈ Nat.divisors d →
      conclusion_fibadic_gcd_convolution_diagonalization_mobius_recover
          (conclusion_fibadic_visible_depth_mobius_primitive_semisimplicity_semisimple_model d) n =
        conclusion_fibadic_visible_depth_mobius_count_exact_count n) ∧
    (conclusion_fibadic_gcd_convolution_diagonalization_invertible_on_support (Nat.divisors d)
        (conclusion_fibadic_visible_depth_mobius_primitive_semisimplicity_semisimple_model d) ↔
      ∀ n, n ∈ Nat.divisors d →
        conclusion_fibadic_visible_depth_mobius_count_exact_count n ≠ 0)

/-- Paper label: `thm:conclusion-fibadic-visible-depth-mobius-primitive-semisimplicity`. The
fibadic exact-depth Möbius packet is already finite on the divisor support of `d`, and the
gcd-projector package acts diagonally on that pointwise model. -/
theorem paper_conclusion_fibadic_visible_depth_mobius_primitive_semisimplicity :
    conclusion_fibadic_visible_depth_mobius_primitive_semisimplicity_statement := by
  intro d
  let S := Nat.divisors d
  let f :=
    conclusion_fibadic_visible_depth_mobius_primitive_semisimplicity_semisimple_model d
  have hf :
      conclusion_fibadic_gcd_convolution_diagonalization_finite_support S f := by
    intro n hn
    dsimp [f]
    simp [conclusion_fibadic_visible_depth_mobius_primitive_semisimplicity_semisimple_model, S, hn]
  have hdiag := paper_conclusion_fibadic_gcd_convolution_diagonalization S f hf
  rcases hdiag with ⟨_, _, hrecover, hinv⟩
  refine ⟨rfl, rfl, hf, ?_, ?_, ?_, ?_⟩
  · intro m n hn
    simp [conclusion_fibadic_gcd_convolution_diagonalization_exact_depth_projector,
      conclusion_fibadic_visible_depth_mobius_primitive_semisimplicity_semisimple_model, hn]
  · intro n hn
    rw [conclusion_fibadic_gcd_convolution_diagonalization_diagonal_coefficient_eq]
    simp [conclusion_fibadic_visible_depth_mobius_primitive_semisimplicity_semisimple_model, hn]
  · intro n hn
    have hrec := hrecover n (by simpa [S] using hn)
    dsimp [f] at hrec
    simpa [conclusion_fibadic_visible_depth_mobius_primitive_semisimplicity_semisimple_model, hn]
      using hrec
  · constructor
    · intro h n hn
      have h' := (hinv.mp h) n (by simpa [S] using hn)
      have hrec := hrecover n (by simpa [S] using hn)
      have hmodel :
          conclusion_fibadic_visible_depth_mobius_primitive_semisimplicity_semisimple_model d n =
            conclusion_fibadic_visible_depth_mobius_count_exact_count n := by
        simp [conclusion_fibadic_visible_depth_mobius_primitive_semisimplicity_semisimple_model, hn]
      dsimp [f] at h' hrec
      rw [hrec, hmodel] at h'
      exact h'
    · intro h
      refine hinv.mpr ?_
      intro n hn
      have hrec := hrecover n hn
      have hmodel :
          conclusion_fibadic_visible_depth_mobius_primitive_semisimplicity_semisimple_model d n =
            conclusion_fibadic_visible_depth_mobius_count_exact_count n := by
        simp [conclusion_fibadic_visible_depth_mobius_primitive_semisimplicity_semisimple_model, S,
          hn]
      dsimp [f] at hrec
      rw [hrec, hmodel]
      simpa [S] using h n (by simpa [S] using hn)

end Omega.Conclusion
