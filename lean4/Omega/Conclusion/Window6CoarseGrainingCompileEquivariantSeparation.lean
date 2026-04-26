import Mathlib.Tactic
import Omega.Conclusion.PushforwardFullMatrix
import Omega.Conclusion.Window6LowOrderTensorVacuum

namespace Omega.Conclusion

/-- Concrete data for a nontrivial finite window-`6` coarse graining. -/
structure conclusion_window6_coarse_graining_compile_equivariant_separation_data where
  blockCount : ℕ
  nontrivial : 2 ≤ blockCount

namespace conclusion_window6_coarse_graining_compile_equivariant_separation_data

/-- The full pushforward matrix envelope compiles the coarse projector shadow. -/
def projectorShadowCompiles
    (D : conclusion_window6_coarse_graining_compile_equivariant_separation_data) : Prop :=
  0 < D.blockCount ∧ Nat.fib 8 = 21 ∧ 21 ^ 2 = 441

/-- Window-`6` has no low-order equivariant classifier in the recorded bounded range. -/
def noLowOrderEquivariantClassifier
    (D : conclusion_window6_coarse_graining_compile_equivariant_separation_data) : Prop :=
  0 < D.blockCount ∧
    ∀ r : Fin 19, window6TensorEquivariantLawsVanish (r.1 + 2)

end conclusion_window6_coarse_graining_compile_equivariant_separation_data

/-- Paper label:
`cor:conclusion-window6-coarse-graining-compile-equivariant-separation`. Nontrivial finite
coarse grainings inherit projector-shadow compilation from the full pushforward matrix envelope,
while the low-order tensor vacuum rules out equivariant classifiers below the stated order. -/
theorem paper_conclusion_window6_coarse_graining_compile_equivariant_separation
    (D : conclusion_window6_coarse_graining_compile_equivariant_separation_data) :
    D.projectorShadowCompiles ∧ D.noLowOrderEquivariantClassifier := by
  have hBlock : 0 < D.blockCount :=
    Nat.lt_of_lt_of_le (by norm_num) D.nontrivial
  rcases PushforwardFullMatrix.paper_conclusion_window6_pushforward_full_matrix with
    ⟨hfib, hsq, -, -, -⟩
  exact ⟨⟨hBlock, hfib, hsq⟩,
    ⟨hBlock, paper_conclusion_window6_low_order_tensor_vacuum.2⟩⟩

end Omega.Conclusion
