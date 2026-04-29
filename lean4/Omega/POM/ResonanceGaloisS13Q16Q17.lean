import Mathlib.GroupTheory.GroupAction.Jordan
import Mathlib.Tactic

namespace Omega.POM

/-- A concrete group-theoretic certificate for the two resonance-window Galois groups.  The
primitive subgroup and transposition inertia data are the inputs needed by Jordan's theorem. -/
structure pom_resonance_galois_s13_q16_17_certificate where
  pom_resonance_galois_s13_q16_17_group16 : Subgroup (Equiv.Perm (Fin 13))
  pom_resonance_galois_s13_q16_17_group17 : Subgroup (Equiv.Perm (Fin 13))
  pom_resonance_galois_s13_q16_17_primitive16 :
    MulAction.IsPreprimitive pom_resonance_galois_s13_q16_17_group16 (Fin 13)
  pom_resonance_galois_s13_q16_17_primitive17 :
    MulAction.IsPreprimitive pom_resonance_galois_s13_q16_17_group17 (Fin 13)
  pom_resonance_galois_s13_q16_17_inertia16 : Equiv.Perm (Fin 13)
  pom_resonance_galois_s13_q16_17_inertia17 : Equiv.Perm (Fin 13)
  pom_resonance_galois_s13_q16_17_inertia16_isSwap :
    pom_resonance_galois_s13_q16_17_inertia16.IsSwap
  pom_resonance_galois_s13_q16_17_inertia17_isSwap :
    pom_resonance_galois_s13_q16_17_inertia17.IsSwap
  pom_resonance_galois_s13_q16_17_inertia16_mem :
    pom_resonance_galois_s13_q16_17_inertia16 ∈
      pom_resonance_galois_s13_q16_17_group16
  pom_resonance_galois_s13_q16_17_inertia17_mem :
    pom_resonance_galois_s13_q16_17_inertia17 ∈
      pom_resonance_galois_s13_q16_17_group17
  pom_resonance_galois_s13_q16_17_ramifiedPrime16 : ℕ
  pom_resonance_galois_s13_q16_17_ramifiedPrime17 : ℕ
  pom_resonance_galois_s13_q16_17_ramifiedPrime16_eq :
    pom_resonance_galois_s13_q16_17_ramifiedPrime16 = 59
  pom_resonance_galois_s13_q16_17_ramifiedPrime17_eq :
    pom_resonance_galois_s13_q16_17_ramifiedPrime17 = 62927
  pom_resonance_galois_s13_q16_17_discValuation16 : ℕ
  pom_resonance_galois_s13_q16_17_discValuation17 : ℕ
  pom_resonance_galois_s13_q16_17_discValuation16_eq :
    pom_resonance_galois_s13_q16_17_discValuation16 = 1
  pom_resonance_galois_s13_q16_17_discValuation17_eq :
    pom_resonance_galois_s13_q16_17_discValuation17 = 1

/-- The certificate concludes that both permutation Galois groups are full `S₁₃`, and records the
simple-discriminant transposition primes from the paper statement. -/
def pom_resonance_galois_s13_q16_17_conclusion
    (D : pom_resonance_galois_s13_q16_17_certificate) : Prop :=
  D.pom_resonance_galois_s13_q16_17_group16 = ⊤ ∧
    D.pom_resonance_galois_s13_q16_17_group17 = ⊤ ∧
    D.pom_resonance_galois_s13_q16_17_ramifiedPrime16 = 59 ∧
    D.pom_resonance_galois_s13_q16_17_ramifiedPrime17 = 62927 ∧
    D.pom_resonance_galois_s13_q16_17_discValuation16 = 1 ∧
    D.pom_resonance_galois_s13_q16_17_discValuation17 = 1

/-- Paper label: `thm:pom-resonance-galois-s13-q16-17`. -/
theorem paper_pom_resonance_galois_s13_q16_17
    (D : pom_resonance_galois_s13_q16_17_certificate) :
    pom_resonance_galois_s13_q16_17_conclusion D := by
  have h16 :
      D.pom_resonance_galois_s13_q16_17_group16 = ⊤ :=
    Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem
      (G := D.pom_resonance_galois_s13_q16_17_group16) (α := Fin 13)
      D.pom_resonance_galois_s13_q16_17_primitive16
      D.pom_resonance_galois_s13_q16_17_inertia16
      D.pom_resonance_galois_s13_q16_17_inertia16_isSwap
      D.pom_resonance_galois_s13_q16_17_inertia16_mem
  have h17 :
      D.pom_resonance_galois_s13_q16_17_group17 = ⊤ :=
    Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem
      (G := D.pom_resonance_galois_s13_q16_17_group17) (α := Fin 13)
      D.pom_resonance_galois_s13_q16_17_primitive17
      D.pom_resonance_galois_s13_q16_17_inertia17
      D.pom_resonance_galois_s13_q16_17_inertia17_isSwap
      D.pom_resonance_galois_s13_q16_17_inertia17_mem
  exact
    ⟨h16, h17, D.pom_resonance_galois_s13_q16_17_ramifiedPrime16_eq,
      D.pom_resonance_galois_s13_q16_17_ramifiedPrime17_eq,
      D.pom_resonance_galois_s13_q16_17_discValuation16_eq,
      D.pom_resonance_galois_s13_q16_17_discValuation17_eq⟩

end Omega.POM
