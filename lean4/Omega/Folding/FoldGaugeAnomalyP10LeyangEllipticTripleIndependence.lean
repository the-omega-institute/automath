import Mathlib
import Omega.Folding.FoldGaugeAnomalyP10EllipticTorsionDisjointness
import Omega.Folding.FoldGaugeAnomalyLeyangEllipticTorsionDisjointness
import Omega.Folding.KilloLeyangTwoBranchFieldsProductGalois

namespace Omega.Folding

/-- The excluded-prime condition says that the torsion support `{37, ℓ}` avoids the three audited
primes appearing in the `P10`/Lee--Yang quadratic data. -/
def fold_gauge_anomaly_p10_leyang_elliptic_triple_independence_excluded_support
    (ℓ : ℕ) : Prop :=
  3 ∉ fold_gauge_anomaly_p10_elliptic_torsion_disjointness_torsion_ramification_support ℓ ∧
    1931 ∉ fold_gauge_anomaly_p10_elliptic_torsion_disjointness_torsion_ramification_support ℓ ∧
    34319 ∉ fold_gauge_anomaly_p10_elliptic_torsion_disjointness_torsion_ramification_support ℓ

/-- Three-channel direct-product package assembled from the existing `P10`/Lee--Yang product and
the two torsion disjointness statements. -/
def fold_gauge_anomaly_p10_leyang_elliptic_triple_independence_product_galois
    (ℓ : ℕ) : Prop :=
  killoLeyangTwoBranchFieldsProductGalois ∧
    fold_gauge_anomaly_p10_elliptic_torsion_disjointness_direct_product_galois ℓ ∧
    paper_fold_gauge_anomaly_leyang_elliptic_torsion_disjointness ∧
    fold_gauge_anomaly_p10_leyang_elliptic_triple_independence_excluded_support ℓ ∧
    killoLeyangTenBranchFieldOrder = Nat.factorial 10 ∧
    killoLeyangCubicBranchFieldOrder = Nat.factorial 3 ∧
    fold_gauge_anomaly_leyang_elliptic_torsion_disjointness_elliptic_torsion_field_order = 480

/-- Density of one conjugacy class inside one factor of the audited three-channel product. -/
def fold_gauge_anomaly_p10_leyang_elliptic_triple_independence_class_density
    (classSize groupOrder : ℕ) : ℚ :=
  (classSize : ℚ) / groupOrder

/-- Product Chebotarev density on the `S₁₀ × S₃ × Gal(M_ℓ/ℚ)` package, with audited torsion image
order `480`. -/
def fold_gauge_anomaly_p10_leyang_elliptic_triple_independence_joint_density
    (C10 C3 Cℓ : ℕ) : ℚ :=
  fold_gauge_anomaly_p10_leyang_elliptic_triple_independence_class_density
      C10 (Nat.factorial 10) *
    fold_gauge_anomaly_p10_leyang_elliptic_triple_independence_class_density
      C3 (Nat.factorial 3) *
    fold_gauge_anomaly_p10_leyang_elliptic_triple_independence_class_density
      Cℓ 480

/-- Paper label: `cor:fold-gauge-anomaly-P10-leyang-elliptic-triple-independence`. Excluding
`ℓ ∈ {3, 1931, 34319}` leaves all three pairwise intersections trivial, so the existing
`P10`/Lee--Yang product and the two torsion disjointness packages combine into the expected
three-channel direct-product and density factorization statement. -/
theorem paper_fold_gauge_anomaly_p10_leyang_elliptic_triple_independence
    (ℓ C10 C3 Cℓ : ℕ) (hℓ3 : ℓ ≠ 3) (hℓ1931 : ℓ ≠ 1931) (hℓ34319 : ℓ ≠ 34319) :
    fold_gauge_anomaly_p10_leyang_elliptic_triple_independence_product_galois ℓ ∧
      fold_gauge_anomaly_p10_leyang_elliptic_triple_independence_joint_density C10 C3 Cℓ =
        (C10 : ℚ) / Nat.factorial 10 * ((C3 : ℚ) / Nat.factorial 3) * ((Cℓ : ℚ) / 480) := by
  have hp10leyang : killoLeyangTwoBranchFieldsProductGalois :=
    (paper_killo_leyang_two_branch_fields_product_galois).2
  have hp10elliptic :=
    paper_fold_gauge_anomaly_p10_elliptic_torsion_disjointness ℓ hℓ1931 hℓ34319
  have hleyangElliptic : paper_fold_gauge_anomaly_leyang_elliptic_torsion_disjointness :=
    fold_gauge_anomaly_leyang_elliptic_torsion_disjointness_certified
  have hExcluded :
      fold_gauge_anomaly_p10_leyang_elliptic_triple_independence_excluded_support ℓ := by
    refine ⟨?_, ?_, ?_⟩
    · simp [fold_gauge_anomaly_p10_elliptic_torsion_disjointness_torsion_ramification_support]
      intro h
      exact hℓ3 h.symm
    · simp [fold_gauge_anomaly_p10_elliptic_torsion_disjointness_torsion_ramification_support]
      intro h
      exact hℓ1931 h.symm
    · simp [fold_gauge_anomaly_p10_elliptic_torsion_disjointness_torsion_ramification_support]
      intro h
      exact hℓ34319 h.symm
  refine
    ⟨⟨hp10leyang, hp10elliptic.2.2.2.2, hleyangElliptic, hExcluded, rfl, rfl, rfl⟩, ?_⟩
  simp [fold_gauge_anomaly_p10_leyang_elliptic_triple_independence_joint_density,
    fold_gauge_anomaly_p10_leyang_elliptic_triple_independence_class_density, mul_assoc]

end Omega.Folding
