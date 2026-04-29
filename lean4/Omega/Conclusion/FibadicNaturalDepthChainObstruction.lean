import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Conclusion.FibadicProfiniteCollapseToZhat
import Omega.Folding.FiberArithmeticProperties

namespace Omega.Conclusion

/-- Paper-facing package for
`thm:conclusion-fibadic-natural-depth-chain-obstruction`. -/
def conclusion_fibadic_natural_depth_chain_obstruction_statement : Prop :=
  (∀ m n : ℕ, 1 ≤ m → m < n →
      ((∃ f : ZMod (Nat.fib (n + 2)) →+* ZMod (Nat.fib (m + 2)), f 1 = 1) ↔
        (m + 2) ∣ (n + 2))) ∧
    (∀ m : ℕ, 1 ≤ m →
      ¬ ∃ f : ZMod (Nat.fib (m + 3)) →+* ZMod (Nat.fib (m + 2)), f 1 = 1) ∧
    ConclusionFibadicProfiniteCollapseToZhat

theorem conclusion_fibadic_natural_depth_chain_obstruction_holds :
    conclusion_fibadic_natural_depth_chain_obstruction_statement := by
  refine ⟨?_, ?_, paper_conclusion_fibadic_profinite_collapse_to_zhat⟩
  · intro m n hm hmn
    have hd : 3 ≤ m + 2 := by omega
    have he : 3 ≤ n + 2 := by omega
    simpa [add_assoc] using
      Omega.paper_finite_resolution_morphism_divisibility_rigidity (m + 2) (n + 2) hd he
  · intro m hm
    intro h
    rcases h with ⟨f, hf⟩
    have hd : 3 ≤ m + 2 := by omega
    have he : 3 ≤ m + 3 := by omega
    have hdiv : (m + 2) ∣ (m + 3) := by
      exact
        (Omega.paper_finite_resolution_morphism_divisibility_rigidity
          (m + 2) (m + 3) hd he).mp ⟨f, hf⟩
    rcases hdiv with ⟨k, hk⟩
    have hkne0 : k ≠ 0 := by
      intro hk0
      rw [hk0, Nat.mul_zero] at hk
      omega
    have hkone : k = 1 := by
      by_contra hknot1
      have hkge : 2 ≤ k := by omega
      have hge : 2 * (m + 2) ≤ (m + 2) * k := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_left (m + 2) hkge
      have hge' : 2 * (m + 2) ≤ m + 3 := by
        simpa [hk] using hge
      have hlt : m + 3 < 2 * (m + 2) := by omega
      exact (Nat.not_le_of_gt hlt) hge'
    have hEq : m + 3 = m + 2 := by simpa [hkone] using hk
    omega

def paper_conclusion_fibadic_natural_depth_chain_obstruction : Prop := by
  exact conclusion_fibadic_natural_depth_chain_obstruction_statement

end Omega.Conclusion
