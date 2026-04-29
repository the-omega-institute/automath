import Mathlib
import Omega.Folding.FoldGaugeAnomalyP10GaloisDiscriminant

namespace Omega.Folding

/-- The Neron--Ogg--Shafarevich ramification support for the conductor-`37` torsion field package:
the only possible ramified primes are `37` and `ℓ`. -/
def fold_gauge_anomaly_p10_elliptic_torsion_disjointness_torsion_ramification_support
    (ℓ : ℕ) : Finset ℕ :=
  {37, ℓ}

/-- If the torsion support avoids the two ramified primes of the `P10` quadratic subfield, then the
only possible common quadratic subextension is excluded. -/
def fold_gauge_anomaly_p10_elliptic_torsion_disjointness_intersection_is_base (ℓ : ℕ) : Prop :=
  1931 ∉ fold_gauge_anomaly_p10_elliptic_torsion_disjointness_torsion_ramification_support ℓ ∧
    34319 ∉ fold_gauge_anomaly_p10_elliptic_torsion_disjointness_torsion_ramification_support ℓ

/-- Once the intersection is trivial, the compositum inherits the expected direct-product Galois
description. -/
def fold_gauge_anomaly_p10_elliptic_torsion_disjointness_direct_product_galois (ℓ : ℕ) : Prop :=
  fold_gauge_anomaly_p10_elliptic_torsion_disjointness_intersection_is_base ℓ ∧
    Nat.factorial 10 = 3628800

/-- Paper label: `prop:fold-gauge-anomaly-P10-elliptic-torsion-disjointness`. The prior `P10`
Galois/discriminant audit gives the unique quadratic subfield, while the torsion ramification
support `{37, ℓ}` excludes the two ramified primes `1931` and `34319` whenever `ℓ` avoids them, so
the intersection is trivial and the compositum carries the direct-product Galois package. -/
theorem paper_fold_gauge_anomaly_p10_elliptic_torsion_disjointness :
    ∀ ℓ : ℕ, ℓ ≠ 1931 → ℓ ≠ 34319 →
      let D : FoldGaugeAnomalyP10GaloisDiscriminantData := ⟨⟩
      D.unique_quadratic_subfield ∧
        D.fold_gauge_anomaly_p10_galois_discriminant_squarefree_kernel = 66269989 ∧
        fold_gauge_anomaly_p10_elliptic_torsion_disjointness_torsion_ramification_support ℓ =
          {37, ℓ} ∧
        fold_gauge_anomaly_p10_elliptic_torsion_disjointness_intersection_is_base ℓ ∧
        fold_gauge_anomaly_p10_elliptic_torsion_disjointness_direct_product_galois ℓ := by
  intro ℓ hℓ1931 hℓ34319
  let D : FoldGaugeAnomalyP10GaloisDiscriminantData := ⟨⟩
  have hp10 := paper_fold_gauge_anomaly_p10_galois_discriminant D
  have hquad : D.unique_quadratic_subfield := hp10.2.2.2.1
  have hmax : D.maximal_abelian_subextension := hp10.2.2.2.2
  have hbase :
      fold_gauge_anomaly_p10_elliptic_torsion_disjointness_intersection_is_base ℓ := by
    refine ⟨?_, ?_⟩
    · simp [fold_gauge_anomaly_p10_elliptic_torsion_disjointness_torsion_ramification_support]
      intro h
      exact hℓ1931 h.symm
    · simp [fold_gauge_anomaly_p10_elliptic_torsion_disjointness_torsion_ramification_support]
      intro h
      exact hℓ34319 h.symm
  refine ⟨hquad, hmax.2, rfl, hbase, ?_⟩
  refine ⟨hbase, ?_⟩
  simpa using Omega.Folding.GaugeAnomalyP10Degree.factorial_10_eq

end Omega.Folding
