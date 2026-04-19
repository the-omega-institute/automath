import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper-facing faithful multiplicative semigroup action built from the stable successor normal
form. The maps `M n` act by multiplying the valuation and then returning to the normal form `Z`. -/
theorem paper_conclusion_stable_successor_faithful_semigroup {X : Type*} (zeroX : X) (S : X → X)
    (Z : ℕ → X) (Val : X → ℕ) (hValZ : ∀ n, Val (Z n) = n)
    (hIter : ∀ n, Z n = Nat.iterate S n zeroX) :
    let M : ℕ → X → X := fun n c => Z (n * Val c)
    ; (∀ c d, M (Val d) c = Nat.iterate S (Val c * Val d) zeroX) ∧
        (∀ m n c, M m (M n c) = M (m * n) c) ∧
        (∀ m n, M m = M n → m = n) := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · intro c d
    rw [hIter, Nat.mul_comm]
  · intro m n c
    simp [hValZ, Nat.mul_assoc]
  · intro m n hEq
    have hAt : Z (m * Val (Z 1)) = Z (n * Val (Z 1)) := congrFun hEq (Z 1)
    have hVal : Val (Z (m * Val (Z 1))) = Val (Z (n * Val (Z 1))) := congrArg Val hAt
    simpa [hValZ] using hVal

end Omega.Conclusion
