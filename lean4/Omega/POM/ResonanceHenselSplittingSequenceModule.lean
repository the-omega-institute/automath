import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-resonance-hensel-splitting-sequence-module`. -/
theorem paper_pom_resonance_hensel_splitting_sequence_module {M : Type} [AddCommGroup M]
    (U V A B : M → M) (f : M) (h_bezout : ∀ x, A (U x) + B (V x) = x)
    (h_nil : U (B (V f)) = 0) (h_unip : V (A (U f)) = 0) :
    ∃ f_nil f_unip : M, f = f_nil + f_unip ∧ U f_nil = 0 ∧ V f_unip = 0 := by
  refine ⟨B (V f), A (U f), ?_, h_nil, h_unip⟩
  calc
    f = A (U f) + B (V f) := (h_bezout f).symm
    _ = B (V f) + A (U f) := by rw [add_comm]

end Omega.POM
