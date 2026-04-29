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

/-- The proper-divisor part of the exact-depth Möbius count, after separating the top divisor
`e = 1`. -/
noncomputable def conclusion_fibadic_exact_depth_characters_dominate_proper_contribution
    (d : ℕ) : ℤ :=
  ∑ e ∈ (Nat.divisors d).filter (fun e => e ≠ 1),
    ArithmeticFunction.moebius e *
      conclusion_fibadic_visible_depth_mobius_count_visible_count (d / e)

/-- Concrete domination package for the exact-depth characters: the exact count is the top
visible Fibonacci packet plus the proper-divisor Möbius remainder, and any uniform half-depth
bound for each proper weighted summand lifts to the full remainder by the divisor count. -/
def conclusion_fibadic_exact_depth_characters_dominate_statement : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    conclusion_fibadic_visible_depth_mobius_count_exact_count d =
      conclusion_fibadic_visible_depth_mobius_count_visible_count d +
        conclusion_fibadic_exact_depth_characters_dominate_proper_contribution d ∧
    ((∀ e : ℕ, e ∈ (Nat.divisors d).filter (fun e => e ≠ 1) →
        (ArithmeticFunction.moebius e *
          conclusion_fibadic_visible_depth_mobius_count_visible_count (d / e)).natAbs ≤
          Nat.fib (d / 2 + 2)) →
      (conclusion_fibadic_exact_depth_characters_dominate_proper_contribution d).natAbs ≤
        ((Nat.divisors d).filter (fun e => e ≠ 1)).card * Nat.fib (d / 2 + 2))

/-- Paper label: `cor:conclusion-fibadic-exact-depth-characters-dominate`. -/
theorem paper_conclusion_fibadic_exact_depth_characters_dominate :
    conclusion_fibadic_exact_depth_characters_dominate_statement := by
  intro d hd
  let f : ℕ → ℤ := fun e =>
    ArithmeticFunction.moebius e *
      conclusion_fibadic_visible_depth_mobius_count_visible_count (d / e)
  have hfilter :
      (Nat.divisors d).filter (fun e => e = 1) = ({1} : Finset ℕ) := by
    ext e
    by_cases he : e = 1
    · subst e
      simp [Nat.mem_divisors, Nat.ne_of_gt hd]
    · simp [he]
  have hsplit :
      ∑ e ∈ Nat.divisors d, f e =
        ∑ e ∈ (Nat.divisors d).filter (fun e => e = 1), f e +
          ∑ e ∈ (Nat.divisors d).filter (fun e => e ≠ 1), f e := by
    simpa [add_comm] using
      (Finset.sum_filter_add_sum_filter_not
        (s := Nat.divisors d) (p := fun e => e = 1) (f := f)).symm
  have hidentity :
      conclusion_fibadic_visible_depth_mobius_count_exact_count d =
        conclusion_fibadic_visible_depth_mobius_count_visible_count d +
          conclusion_fibadic_exact_depth_characters_dominate_proper_contribution d := by
    calc
      conclusion_fibadic_visible_depth_mobius_count_exact_count d =
          ∑ e ∈ Nat.divisors d, f e := by
            simp [conclusion_fibadic_visible_depth_mobius_count_exact_count, f]
      _ = ∑ e ∈ (Nat.divisors d).filter (fun e => e = 1), f e +
          ∑ e ∈ (Nat.divisors d).filter (fun e => e ≠ 1), f e := hsplit
      _ = conclusion_fibadic_visible_depth_mobius_count_visible_count d +
          conclusion_fibadic_exact_depth_characters_dominate_proper_contribution d := by
            simp [hfilter, conclusion_fibadic_exact_depth_characters_dominate_proper_contribution,
              f]
  refine ⟨hidentity, ?_⟩
  intro hsummand
  let S := (Nat.divisors d).filter (fun e => e ≠ 1)
  let B := Nat.fib (d / 2 + 2)
  have hsum_bound :
      ∀ s : Finset ℕ, (∀ e : ℕ, e ∈ s → (f e).natAbs ≤ B) →
        (∑ e ∈ s, f e).natAbs ≤ s.card * B := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _h
      simp
    · intro a s has ih hlocal
      rw [Finset.sum_insert has, Finset.card_insert_of_notMem has]
      have ha : (f a).natAbs ≤ B := hlocal a (by simp)
      have hs : (∑ e ∈ s, f e).natAbs ≤ s.card * B := by
        exact ih (fun e he => hlocal e (by simp [he]))
      have htri : (f a + ∑ e ∈ s, f e).natAbs ≤ (f a).natAbs + (∑ e ∈ s, f e).natAbs :=
        Int.natAbs_add_le (f a) (∑ e ∈ s, f e)
      calc
        (f a + ∑ e ∈ s, f e).natAbs ≤
            (f a).natAbs + (∑ e ∈ s, f e).natAbs := htri
        _ ≤ B + s.card * B := Nat.add_le_add ha hs
        _ = (s.card + 1) * B := by ring
  have hS : ∀ e : ℕ, e ∈ S → (f e).natAbs ≤ B := by
    intro e he
    exact hsummand e (by simpa [S, B, f] using he)
  simpa [S, B, conclusion_fibadic_exact_depth_characters_dominate_proper_contribution, f] using
    hsum_bound S hS

end Omega.Conclusion
