import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Smith loss for a modulus, written as a finite sum over the prime-factor exponent ledger. -/
def conclusion_smith_loss_modularity_divisibility_lattice_loss {m : ℕ}
    (smithValuation : Fin m → ℕ → ℕ) (rankGap n : ℕ) : ℕ :=
  rankGap +
    n.factorization.sum fun p e =>
      ∑ i : Fin m, smithValuation i p * e

private lemma conclusion_smith_loss_modularity_divisibility_lattice_weighted_sum_add {m : ℕ}
    (smithValuation : Fin m → ℕ → ℕ) (f g : ℕ →₀ ℕ) :
    (f + g).sum (fun p e => ∑ i : Fin m, smithValuation i p * e) =
      f.sum (fun p e => ∑ i : Fin m, smithValuation i p * e) +
        g.sum (fun p e => ∑ i : Fin m, smithValuation i p * e) := by
  classical
  exact Finsupp.sum_add_index'
    (h := fun p e => ∑ i : Fin m, smithValuation i p * e)
    (by simp)
    (by
      intro p e₁ e₂
      simp [mul_add, Finset.sum_add_distrib])

/-- Paper label: `thm:conclusion-smith-loss-modularity-divisibility-lattice`. -/
theorem paper_conclusion_smith_loss_modularity_divisibility_lattice {m : ℕ}
    (smithValuation : Fin m → ℕ → ℕ) (rankGap b c : ℕ) (hb : 0 < b) (hc : 0 < c) :
    conclusion_smith_loss_modularity_divisibility_lattice_loss smithValuation rankGap
        (Nat.lcm b c) +
      conclusion_smith_loss_modularity_divisibility_lattice_loss smithValuation rankGap
        (Nat.gcd b c) =
      conclusion_smith_loss_modularity_divisibility_lattice_loss smithValuation rankGap b +
        conclusion_smith_loss_modularity_divisibility_lattice_loss smithValuation rankGap c := by
  classical
  let W : (ℕ →₀ ℕ) → ℕ :=
    fun f => f.sum fun p e => ∑ i : Fin m, smithValuation i p * e
  have hb0 : b ≠ 0 := Nat.ne_of_gt hb
  have hc0 : c ≠ 0 := Nat.ne_of_gt hc
  have hfactor :
      (Nat.lcm b c).factorization + (Nat.gcd b c).factorization =
        b.factorization + c.factorization := by
    ext p
    simp [Nat.factorization_lcm hb0 hc0, Nat.factorization_gcd hb0 hc0,
      Finsupp.sup_apply, Finsupp.inf_apply, max_add_min]
  have hsum :
      W (Nat.lcm b c).factorization + W (Nat.gcd b c).factorization =
        W b.factorization + W c.factorization := by
    calc
      W (Nat.lcm b c).factorization + W (Nat.gcd b c).factorization
          = W ((Nat.lcm b c).factorization + (Nat.gcd b c).factorization) := by
              exact
                (conclusion_smith_loss_modularity_divisibility_lattice_weighted_sum_add
                  smithValuation (Nat.lcm b c).factorization
                  (Nat.gcd b c).factorization).symm
      _ = W (b.factorization + c.factorization) := by rw [hfactor]
      _ = W b.factorization + W c.factorization := by
              exact
                conclusion_smith_loss_modularity_divisibility_lattice_weighted_sum_add
                  smithValuation b.factorization c.factorization
  simp [conclusion_smith_loss_modularity_divisibility_lattice_loss, W] at hsum ⊢
  omega

end Omega.Conclusion
