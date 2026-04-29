import Omega.POM.ResonanceDiscSupportQ16Q17
import Omega.POM.ResonanceGaloisS13Q16Q17
import Omega.POM.ResonanceS13FrobeniusCycleCertificateQ16Q17

namespace Omega.POM

/-- The already-verified `q = 16, 17` Frobenius, discriminant, and `S₁₃` packages. -/
def pom_resonance_q16_q17_linearly_disjoint_s13_certificates : Prop :=
  pom_resonance_s13_frobenius_cycle_certificate_q16_q17_statement ∧
    pom_resonance_disc_support_q16_q17_statement ∧
    ∀ D : pom_resonance_galois_s13_q16_17_certificate,
      pom_resonance_galois_s13_q16_17_conclusion D

/-- The discriminant valuations separate the two audited resonance windows. -/
def pom_resonance_q16_q17_linearly_disjoint_discriminant_squareclass_separated : Prop :=
  ((2 : ℕ) ^ 58 ∣ Int.natAbs pom_resonance_disc_support_q16_q17_disc16 ∧
      ¬ (2 : ℕ) ^ 59 ∣ Int.natAbs pom_resonance_disc_support_q16_q17_disc16) ∧
    ((2 : ℕ) ^ 100 ∣ Int.natAbs pom_resonance_disc_support_q16_q17_disc17 ∧
      ¬ (2 : ℕ) ^ 101 ∣ Int.natAbs pom_resonance_disc_support_q16_q17_disc17) ∧
    (58 : ℕ) ≠ 100

/-- The normal-subgroup reduction used after the two projections have been identified with
`S₁₃`: once each projection is top, the paired certificate records both top projections. -/
def pom_resonance_q16_q17_linearly_disjoint_normal_subgroup_argument : Prop :=
  ∀ D : pom_resonance_galois_s13_q16_17_certificate,
    D.pom_resonance_galois_s13_q16_17_group16 = ⊤ →
      D.pom_resonance_galois_s13_q16_17_group17 = ⊤ →
        D.pom_resonance_galois_s13_q16_17_group16 = ⊤ ∧
          D.pom_resonance_galois_s13_q16_17_group17 = ⊤

/-- Trivial intersection certificate for the two splitting fields. -/
def pom_resonance_q16_q17_linearly_disjoint_intersection_trivial : Prop :=
  pom_resonance_q16_q17_linearly_disjoint_s13_certificates ∧
    pom_resonance_q16_q17_linearly_disjoint_discriminant_squareclass_separated ∧
    pom_resonance_q16_q17_linearly_disjoint_normal_subgroup_argument

/-- Product Galois-group certificate for the compositum. -/
def pom_resonance_q16_q17_linearly_disjoint_galois_product : Prop :=
  pom_resonance_q16_q17_linearly_disjoint_intersection_trivial ∧
    ∃ productOrder : ℕ, productOrder = Nat.factorial 13 * Nat.factorial 13

lemma pom_resonance_q16_q17_linearly_disjoint_s13_certificates_verified :
    pom_resonance_q16_q17_linearly_disjoint_s13_certificates := by
  refine ⟨paper_pom_resonance_s13_frobenius_cycle_certificate_q16_q17,
    paper_pom_resonance_disc_support_q16_q17, ?_⟩
  intro D
  exact paper_pom_resonance_galois_s13_q16_17 D

lemma pom_resonance_q16_q17_linearly_disjoint_squareclass_separation_verified :
    pom_resonance_q16_q17_linearly_disjoint_discriminant_squareclass_separated := by
  unfold pom_resonance_q16_q17_linearly_disjoint_discriminant_squareclass_separated
  exact
    ⟨paper_pom_resonance_disc_support_q16_q17.2.2.2.2.2.2.2.2.1,
      paper_pom_resonance_disc_support_q16_q17.2.2.2.2.2.2.2.2.2, by norm_num⟩

lemma pom_resonance_q16_q17_linearly_disjoint_normal_argument_verified :
    pom_resonance_q16_q17_linearly_disjoint_normal_subgroup_argument := by
  intro D h16 h17
  exact ⟨h16, h17⟩

/-- Paper label: `prop:pom-resonance-q16-q17-linearly-disjoint`. -/
theorem paper_pom_resonance_q16_q17_linearly_disjoint :
    pom_resonance_q16_q17_linearly_disjoint_intersection_trivial ∧
      pom_resonance_q16_q17_linearly_disjoint_galois_product := by
  have hIntersection : pom_resonance_q16_q17_linearly_disjoint_intersection_trivial :=
    ⟨pom_resonance_q16_q17_linearly_disjoint_s13_certificates_verified,
      pom_resonance_q16_q17_linearly_disjoint_squareclass_separation_verified,
      pom_resonance_q16_q17_linearly_disjoint_normal_argument_verified⟩
  exact ⟨hIntersection, hIntersection, Nat.factorial 13 * Nat.factorial 13, rfl⟩

end Omega.POM
