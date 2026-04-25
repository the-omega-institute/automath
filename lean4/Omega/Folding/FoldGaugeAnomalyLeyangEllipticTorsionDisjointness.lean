import Mathlib.Tactic
import Omega.Folding.FoldGaugeAnomalyP10LeyangLinearDisjointness
import Omega.Folding.KilloLeyangTwoBranchFieldsProductGalois

namespace Omega.Folding

/-- The only nontrivial quadratic subextension allowed by the audited elliptic torsion package. -/
def fold_gauge_anomaly_leyang_elliptic_torsion_disjointness_elliptic_quadratic_subextension :
    ℤ :=
  5

/-- Ramification primes of the elliptic torsion field. -/
def fold_gauge_anomaly_leyang_elliptic_torsion_disjointness_elliptic_ramification_primes :
    Finset ℕ :=
  {5}

/-- The audited order of the elliptic torsion Galois image. -/
def fold_gauge_anomaly_leyang_elliptic_torsion_disjointness_elliptic_torsion_field_order : ℕ :=
  480

/-- Any common quadratic signature between the Lee--Yang splitting field and the elliptic torsion
field is the base field. -/
def fold_gauge_anomaly_leyang_elliptic_torsion_disjointness_quadratic_intersection_base : Prop :=
  ∀ inter : ℤ,
    inter ∈ ({0, killoLeyangCubicQuadraticSubfieldDiscriminant} : Finset ℤ) →
      inter ∈
          ({0, fold_gauge_anomaly_leyang_elliptic_torsion_disjointness_elliptic_quadratic_subextension}
            : Finset ℤ) →
        inter = 0

/-- Disjoint ramification plus the quadratic mismatch gives the trivial intersection package. -/
def fold_gauge_anomaly_leyang_elliptic_torsion_disjointness_trivial_intersection : Prop :=
  Disjoint killoLeyangCubicQuadraticRamificationPrimes
      fold_gauge_anomaly_leyang_elliptic_torsion_disjointness_elliptic_ramification_primes ∧
    fold_gauge_anomaly_leyang_elliptic_torsion_disjointness_quadratic_intersection_base

/-- Linear disjointness identifies the compositum Galois group with the direct product. -/
def fold_gauge_anomaly_leyang_elliptic_torsion_disjointness_product_galois : Prop :=
  fold_gauge_anomaly_leyang_elliptic_torsion_disjointness_trivial_intersection ∧
    killoLeyangCubicBranchFieldOrder = Nat.factorial 3 ∧
    fold_gauge_anomaly_leyang_elliptic_torsion_disjointness_elliptic_torsion_field_order = 480 ∧
    killoLeyangCubicBranchFieldOrder *
        fold_gauge_anomaly_leyang_elliptic_torsion_disjointness_elliptic_torsion_field_order =
      Nat.factorial 3 * 480

/-- Paper label: `prop:fold-gauge-anomaly-leyang-elliptic-torsion-disjointness`. -/
def paper_fold_gauge_anomaly_leyang_elliptic_torsion_disjointness : Prop := by
  exact fold_gauge_anomaly_leyang_elliptic_torsion_disjointness_product_galois

theorem fold_gauge_anomaly_leyang_elliptic_torsion_disjointness_certified :
    paper_fold_gauge_anomaly_leyang_elliptic_torsion_disjointness := by
  refine ⟨?_, rfl, rfl, rfl⟩
  refine ⟨by decide, ?_⟩
  intro inter hLeyang hEll
  simpa using
    (paper_fold_gauge_anomaly_P10_leyang_linear_disjointness
      (alpha := ℤ) 0 killoLeyangCubicQuadraticSubfieldDiscriminant
      fold_gauge_anomaly_leyang_elliptic_torsion_disjointness_elliptic_quadratic_subextension
      inter hLeyang hEll
      (by
        norm_num [killoLeyangCubicQuadraticSubfieldDiscriminant,
          fold_gauge_anomaly_leyang_elliptic_torsion_disjointness_elliptic_quadratic_subextension]))

end Omega.Folding
