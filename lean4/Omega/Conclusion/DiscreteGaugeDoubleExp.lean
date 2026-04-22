import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic
import Omega.Folding.FoldCollisionSandwich

namespace Omega.Conclusion

open scoped BigOperators

/-- Fiberwise discrete gauge proxy `∏_w |S_{d_m(w)}| = ∏_w d_m(w)!`. -/
noncomputable def conclusion_discrete_gauge_double_exp_fiberwise_proxy (m : ℕ) : ℕ :=
  ∏ x : Omega.X m, Nat.factorial (Omega.X.fiberMultiplicity x)

/-- Uniform max-fiber proxy obtained by replacing every block size with the extremal size `D_m`. -/
noncomputable def conclusion_discrete_gauge_double_exp_uniform_proxy (m : ℕ) : ℕ :=
  ∏ _x : Omega.X m, Nat.factorial (Omega.X.maxFiberMultiplicity m)

/-- Paper label: `prop:conclusion-discrete-gauge-double-exp`. The fiberwise symmetric-group
product is bounded by the uniform max-fiber proxy, and that proxy is the factorial of `D_m`
raised to `|X_m| = F_{m+2}`. Since `D_m ≤ 2^m`, this yields the explicit factorial-power upper
envelope expected for the discrete gauge sector. -/
theorem paper_conclusion_discrete_gauge_double_exp (m : ℕ) :
    conclusion_discrete_gauge_double_exp_fiberwise_proxy m ≤
      conclusion_discrete_gauge_double_exp_uniform_proxy m ∧
      conclusion_discrete_gauge_double_exp_uniform_proxy m =
        Nat.factorial (Omega.X.maxFiberMultiplicity m) ^ Nat.fib (m + 2) ∧
      conclusion_discrete_gauge_double_exp_uniform_proxy m ≤
        Nat.factorial (2 ^ m) ^ Nat.fib (m + 2) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold conclusion_discrete_gauge_double_exp_fiberwise_proxy
      conclusion_discrete_gauge_double_exp_uniform_proxy
    exact Finset.prod_le_prod
      (fun x _ => Nat.zero_le _)
      (fun x _ => Nat.factorial_le (Omega.X.fiberMultiplicity_le_max x))
  · simp [conclusion_discrete_gauge_double_exp_uniform_proxy, Finset.prod_const, Omega.X.card_eq_fib]
  · have hpow :
        Nat.factorial (Omega.X.maxFiberMultiplicity m) ^ Fintype.card (Omega.X m) ≤
          Nat.factorial (2 ^ m) ^ Fintype.card (Omega.X m) := by
      exact Nat.pow_le_pow_left
        (Nat.factorial_le (Omega.Folding.maxFiberMultiplicity_le_wordcount m))
        (Fintype.card (Omega.X m))
    simpa [conclusion_discrete_gauge_double_exp_uniform_proxy, Finset.prod_const, Omega.X.card_eq_fib]
      using hpow

end Omega.Conclusion
