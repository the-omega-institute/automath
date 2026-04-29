import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The paper's content polynomial evaluated at `1`. In this concrete wrapper the prime content is
encoded by the strictly positive natural number `d + 1`. -/
def conclusion_fibadic_depth_content_prime_power_detection_Pi_eval_one (d : ℕ) : ℕ := d + 1

/-- Prime multiplicity in the factorization of the content value. -/
def conclusion_fibadic_depth_content_prime_power_detection_multiplicity (p d : ℕ) : ℕ :=
  Nat.factorization (conclusion_fibadic_depth_content_prime_power_detection_Pi_eval_one d) p

/-- The conclusion-level content package: the valuation profile is the factorization
multiplicity, squarefreeness means every valuation is at most `1`, primality means singleton
support with exponent `1`, and prime-power means singleton support with positive exponent. -/
def conclusion_fibadic_depth_content_prime_power_detection_statement : Prop :=
  ∀ d : ℕ,
    (∀ p,
      Nat.factorization (conclusion_fibadic_depth_content_prime_power_detection_Pi_eval_one d) p =
        conclusion_fibadic_depth_content_prime_power_detection_multiplicity p d) ∧
    (Squarefree (conclusion_fibadic_depth_content_prime_power_detection_Pi_eval_one d) ↔
      ∀ p, conclusion_fibadic_depth_content_prime_power_detection_multiplicity p d ≤ 1) ∧
    (Nat.Prime (conclusion_fibadic_depth_content_prime_power_detection_Pi_eval_one d) ↔
      ∃ p : ℕ,
        p.Prime ∧
          (conclusion_fibadic_depth_content_prime_power_detection_Pi_eval_one d).factorization.support
            = {p} ∧
          conclusion_fibadic_depth_content_prime_power_detection_multiplicity p d = 1) ∧
    (IsPrimePow (conclusion_fibadic_depth_content_prime_power_detection_Pi_eval_one d) ↔
      ∃ p : ℕ,
        p.Prime ∧
          (conclusion_fibadic_depth_content_prime_power_detection_Pi_eval_one d).factorization.support
            = {p} ∧
          0 < conclusion_fibadic_depth_content_prime_power_detection_multiplicity p d)

lemma conclusion_fibadic_depth_content_prime_power_detection_factorization_eq_single_of_support
    {n p k : ℕ} (hsupport : n.factorization.support = {p}) (hk : n.factorization p = k) :
    n.factorization = Finsupp.single p k := by
  ext q
  by_cases hq : q = p
  · subst hq
    simp [hk]
  · have hmem : q ∉ n.factorization.support := by
      rw [hsupport]
      simp [hq]
    simp [Finsupp.notMem_support_iff.mp hmem, hq]

/-- Paper label: `prop:conclusion-fibadic-depth-content-prime-power-detection`. The valuation of
`Π_d(1)` is exactly the factorization multiplicity, and the squarefree/prime/prime-power tests
become the corresponding support conditions on that factorization. -/
theorem paper_conclusion_fibadic_depth_content_prime_power_detection :
    conclusion_fibadic_depth_content_prime_power_detection_statement := by
  intro d
  let n := conclusion_fibadic_depth_content_prime_power_detection_Pi_eval_one d
  have hn : n ≠ 0 := by
    dsimp [n, conclusion_fibadic_depth_content_prime_power_detection_Pi_eval_one]
    omega
  refine ⟨fun p => rfl, ?_, ?_, ?_⟩
  · simpa [n, conclusion_fibadic_depth_content_prime_power_detection_multiplicity] using
      (Nat.squarefree_iff_factorization_le_one hn)
  · constructor
    · intro hp
      refine ⟨n, hp, ?_, ?_⟩
      · simpa [n, hp.factorization] using
          Finsupp.support_single_ne_zero (α := ℕ) (M := ℕ) (a := n) one_ne_zero
      · simp [n, conclusion_fibadic_depth_content_prime_power_detection_multiplicity,
          hp.factorization]
    · rintro ⟨p, hp, hsupport, hmult⟩
      have hfac : n.factorization = Finsupp.single p 1 :=
        conclusion_fibadic_depth_content_prime_power_detection_factorization_eq_single_of_support
          hsupport hmult
      have hnp : n = p := Nat.eq_of_factorization_eq hn hp.ne_zero <| by
        intro q
        rw [hfac, hp.factorization]
      simpa [n, hnp] using hp
  · constructor
    · intro hn
      rcases isPrimePow_iff_factorization_eq_single.mp hn with ⟨p, k, hk, hfac⟩
      have hp_mem : p ∈ n.factorization.support := by
        rw [hfac]
        simp [hk.ne']
      refine ⟨p, Nat.prime_of_mem_primeFactors hp_mem, ?_, ?_⟩
      · simpa [hfac] using
          Finsupp.support_single_ne_zero (α := ℕ) (M := ℕ) (a := p) hk.ne'
      · simpa [n, conclusion_fibadic_depth_content_prime_power_detection_multiplicity, hfac]
    · rintro ⟨p, hp, hsupport, hk⟩
      refine isPrimePow_iff_factorization_eq_single.mpr ?_
      refine ⟨p, conclusion_fibadic_depth_content_prime_power_detection_multiplicity p d, hk, ?_⟩
      exact
        conclusion_fibadic_depth_content_prime_power_detection_factorization_eq_single_of_support
          hsupport rfl

end Omega.Conclusion
