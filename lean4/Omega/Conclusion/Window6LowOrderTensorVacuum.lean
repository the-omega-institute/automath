import Mathlib.Tactic
import Omega.GU.Window6PushEnvelopeCertificateUpgrade

namespace Omega.Conclusion

/-- The ambient dimension of the standard module identified by the upgraded window-`6`
Lie-envelope certificate. -/
def window6StandardModuleDimension : ℕ :=
  Omega.GU.window6PushEnvelopeCertificate.ambientDimension

/-- The invariant tensors in degree `r` vanish unless the center acts trivially, i.e. unless the
standard-module dimension divides `r`. -/
def window6TensorInvariantsVanish (r : ℕ) : Prop :=
  ¬ window6StandardModuleDimension ∣ r

/-- An equivariant law `V^⊗r → V` can only survive the center action if the standard-module
dimension divides `r - 1`. -/
def window6TensorEquivariantLawsVanish (r : ℕ) : Prop :=
  ¬ window6StandardModuleDimension ∣ (r - 1)

private theorem window6_standard_module_dimension_eq :
    window6StandardModuleDimension = 21 := by
  exact Omega.GU.paper_window6_push_envelope_certificate_upgrade.1.2.2.1

private theorem not_dvd_twentyone_of_pos_lt {n : ℕ} (hn0 : 0 < n) (hn21 : n < 21) :
    ¬ 21 ∣ n := by
  intro hdiv
  exact Nat.not_le_of_gt hn21 (Nat.le_of_dvd hn0 hdiv)

private theorem window6_tensor_invariants_vanish_of_lt {r : ℕ} (hr0 : 0 < r) (hr21 : r < 21) :
    window6TensorInvariantsVanish r := by
  rw [window6TensorInvariantsVanish, window6_standard_module_dimension_eq]
  exact not_dvd_twentyone_of_pos_lt hr0 hr21

private theorem window6_tensor_equivariant_laws_vanish_of_lt
    {r : ℕ} (hr1 : 0 < r - 1) (hr21 : r - 1 < 21) : window6TensorEquivariantLawsVanish r := by
  rw [window6TensorEquivariantLawsVanish, window6_standard_module_dimension_eq]
  exact not_dvd_twentyone_of_pos_lt hr1 hr21

/-- Low tensor powers of the window-`6` standard module carry neither invariants nor equivariant
laws in the listed bounded ranges: the center-scalar divisibility obstructions `21 ∣ r` and
`21 ∣ (r - 1)` are impossible there.
    thm:conclusion-window6-low-order-tensor-vacuum -/
theorem paper_conclusion_window6_low_order_tensor_vacuum :
    (∀ r : Fin 20, window6TensorInvariantsVanish (r.1 + 1)) ∧
      (∀ r : Fin 19, window6TensorEquivariantLawsVanish (r.1 + 2)) := by
  refine ⟨?_, ?_⟩
  · intro r
    apply window6_tensor_invariants_vanish_of_lt
    · omega
    · omega
  · intro r
    have hrpos : 0 < (r.1 + 2) - 1 := by omega
    have hrlt : (r.1 + 2) - 1 < 21 := by omega
    exact window6_tensor_equivariant_laws_vanish_of_lt hrpos hrlt

end Omega.Conclusion
