import Omega.Folding.FoldCriticalResonanceConstantIntegerLadder

namespace Omega.Folding

/-- Paper label: `cor:fold-collision-gap-resonance-ladder-U`.
The integer resonance ladder supplies the distinguished collision modes `0` and `±k_m(u)`,
where `k_m(u)` is the canonical representative of `u F_m` modulo `F_{m+2}`. -/
theorem paper_fold_collision_gap_resonance_ladder_u (u : ℤ) :
    ∀ m : ℕ, 1 ≤ m →
      let k := foldCriticalResonanceIntegerRepresentative u m
      0 ≤ k ∧
        k < Nat.fib (m + 2) ∧
        k ≡ u * Nat.fib m [ZMOD Nat.fib (m + 2)] ∧
        (-k) ≡ -(u * Nat.fib m) [ZMOD Nat.fib (m + 2)] ∧
        (0 : ℤ) ≡ 0 [ZMOD Nat.fib (m + 2)] := by
  intro m hm
  dsimp
  rcases paper_fold_critical_resonance_constant_integer_ladder u m hm with ⟨hk0, hkFib, hkMod⟩
  refine ⟨hk0, hkFib, hkMod, hkMod.neg, Int.ModEq.refl 0⟩

end Omega.Folding
