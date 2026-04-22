import Mathlib.Tactic
import Omega.GU.Window6LieEnvelopeSL21

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-typelayer-tensor-indecomposability`.
The window-`6` Lie-envelope certificate identifies the ambient simple envelope as `sl(21)` of
dimension `440`. For a nontrivial tensor splitting `21 = m n` with `1 < m, n < 21`, the only
possible factor pairs are `(3, 7)` and `(7, 3)`, and in either case `m^2 + n^2 - 1 = 57 < 440`.
-/
theorem paper_conclusion_window6_typelayer_tensor_indecomposability :
    ∀ m n : ℕ, 1 < m → 1 < n → m < 21 → n < 21 → m * n = 21 → m ^ 2 + n ^ 2 - 1 < 440 := by
  intro m n hm hn hm21 hn21 hmn
  have h440 : Omega.GU.window6PushEnvelopeCertificate.fullDimension = 440 :=
    Omega.GU.paper_window6_lie_envelope_sl21.2.2.2
  rw [← h440]
  interval_cases m <;> interval_cases n <;> omega

end Omega.Conclusion
