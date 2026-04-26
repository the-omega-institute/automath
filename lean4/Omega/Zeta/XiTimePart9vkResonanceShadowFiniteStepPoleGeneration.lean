import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part9vk-resonance-shadow-finite-step-pole-generation`. -/
theorem paper_xi_time_part9vk_resonance_shadow_finite_step_pole_generation
    (S term : ℕ → ℂ → ℂ) (hS1 : S 1 = term 2)
    (hrec : ∀ N, 1 ≤ N → S (N + 1) = fun z => S N z + term (N + 2) z) :
    ∀ N, 1 ≤ N → S N = fun z => ∑ n ∈ Finset.Icc 2 (N + 1), term n z := by
  refine Nat.le_induction ?base ?step
  · ext z
    simp [hS1]
  · intro N hN hsum
    ext z
    calc
      S (N + 1) z = S N z + term (N + 2) z := by
        exact congrFun (hrec N hN) z
      _ = (∑ n ∈ Finset.Icc 2 (N + 1), term n z) + term (N + 2) z := by
        rw [congrFun hsum z]
      _ = ∑ n ∈ Finset.Icc 2 ((N + 1) + 1), term n z := by
        rw [Finset.sum_Icc_succ_top (a := 2) (b := N + 1) (by omega)
          (fun n => term n z)]

end Omega.Zeta
