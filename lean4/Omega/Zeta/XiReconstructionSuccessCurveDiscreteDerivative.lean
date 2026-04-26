import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-reconstruction-success-curve-discrete-derivative`. The discrete
derivative of the capped reconstruction-success curve counts exactly the fibers whose depth
exceeds the current cutoff. -/
theorem paper_xi_reconstruction_success_curve_discrete_derivative
    {ι : Type*} [Fintype ι] (d : ι → ℕ) (M : ℕ) :
    (∑ x : ι, Nat.min (d x) (M + 1)) - (∑ x : ι, Nat.min (d x) M) =
      Fintype.card {x : ι // M + 1 ≤ d x} := by
  classical
  have hpoint :
      ∀ x : ι,
        Nat.min (d x) (M + 1) =
          Nat.min (d x) M + if M + 1 ≤ d x then 1 else 0 := by
    intro x
    by_cases hx : M + 1 ≤ d x
    · have hM : M ≤ d x := Nat.le_trans (Nat.le_succ M) hx
      simp [Nat.min_eq_right hM, hx]
    · have hdx : d x ≤ M := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hx)
      have hdx_succ : d x ≤ M + 1 := le_trans hdx (Nat.le_succ M)
      simp [Nat.min_eq_left hdx, Nat.min_eq_left hdx_succ, hx]
  calc
    (∑ x : ι, Nat.min (d x) (M + 1)) - (∑ x : ι, Nat.min (d x) M)
        = (∑ x : ι, (Nat.min (d x) M + if M + 1 ≤ d x then 1 else 0)) -
            (∑ x : ι, Nat.min (d x) M) := by
          rw [Finset.sum_congr rfl (fun x _ => hpoint x)]
    _ = ∑ x : ι, if M + 1 ≤ d x then 1 else 0 := by
          rw [Finset.sum_add_distrib]
          exact Nat.add_sub_cancel_left _ _
    _ = Fintype.card {x : ι // M + 1 ≤ d x} := by
          simp [Fintype.card_subtype]

end Omega.Zeta
