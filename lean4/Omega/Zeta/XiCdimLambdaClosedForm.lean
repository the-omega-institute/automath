import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic

namespace Omega.Zeta

/-- The closed-form residual-size function obtained by keeping the first `t - k` invariant
factors of a finite abelian group. -/
def xiCdimLambda (factors : List ℕ) (k : ℕ) : ℕ :=
  (factors.take (factors.length - k)).prod

private lemma list_prod_pos_of_forall_pos :
    ∀ {factors : List ℕ}, (∀ n ∈ factors, 0 < n) → 0 < factors.prod
  | [], _ => by simp
  | a :: as, hpos => by
      have ha : 0 < a := hpos a (by simp)
      have htail : 0 < as.prod := list_prod_pos_of_forall_pos (factors := as) (by
        intro n hn
        exact hpos n (by simp [hn]))
      simpa using Nat.mul_pos ha htail

/-- Paper label: `thm:xi-cdim-lambda-closed-form`.
For a list of invariant factors `n₁, …, n_t` with each `nᵢ > 1`, the residual-order function
`Λ_F(k)` is the product of the first `t - k` factors. Splitting the list into its head and tail
recovers the full group order, and `Λ_F(k) = 1` exactly once the phase budget reaches the full
generator count `t`. -/
theorem paper_xi_cdim_lambda_closed_form (factors : List ℕ)
    (hfac : ∀ n ∈ factors, 1 < n) :
    (∀ k : ℕ, xiCdimLambda factors k = (factors.take (factors.length - k)).prod) ∧
      (∀ k : ℕ, k ≤ factors.length →
        xiCdimLambda factors k * (factors.drop (factors.length - k)).prod = factors.prod) ∧
      (∀ k : ℕ, xiCdimLambda factors k = 1 ↔ factors.length ≤ k) := by
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · intro k hk
    simpa [xiCdimLambda] using
      congrArg List.prod (List.take_append_drop (factors.length - k) factors)
  · intro k
    constructor
    · intro hkone
      by_contra hk
      have hlt : k < factors.length := Nat.lt_of_not_ge hk
      cases factors with
      | nil =>
          simp at hlt
      | cons a as =>
          have ha : 1 < a := hfac a (by simp)
          have hk' : k ≤ as.length := Nat.lt_succ_iff.mp hlt
          have hsub : (a :: as).length - k = (as.length - k) + 1 := by
            simpa using Nat.succ_sub hk'
          have htail_pos : 0 < (as.take (as.length - k)).prod := by
            apply list_prod_pos_of_forall_pos
            intro n hn
            have hn_as : n ∈ as := (List.take_sublist (as.length - k) as).subset hn
            have hn_fac : n ∈ a :: as := by simp [hn_as]
            exact lt_trans zero_lt_one (hfac n hn_fac)
          have hmul : 1 < a * (as.take (as.length - k)).prod := by
            exact lt_of_lt_of_le ha (Nat.le_mul_of_pos_right a htail_pos)
          have hgt : 1 < xiCdimLambda (a :: as) k := by
            rw [xiCdimLambda, hsub]
            simpa using hmul
          exact (Nat.ne_of_gt hgt) hkone
    · intro hk
      simp [xiCdimLambda, Nat.sub_eq_zero_of_le hk]

end Omega.Zeta
