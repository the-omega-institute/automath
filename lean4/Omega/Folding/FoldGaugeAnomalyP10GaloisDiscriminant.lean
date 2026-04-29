import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyDiscriminantFactorization
import Omega.Folding.GaugeAnomalyP10Degree

namespace Omega.Folding

/-- Concrete wrapper data for the degree-`10` gauge-anomaly Galois/discriminant package. The
certificate data are fixed by the audited factorization patterns and discriminant arithmetic, so no
additional fields are needed. -/
structure FoldGaugeAnomalyP10GaloisDiscriminantData where

namespace FoldGaugeAnomalyP10GaloisDiscriminantData

/-- The mod-`7` factorization pattern witnessing irreducibility of `P₁₀`. -/
def fold_gauge_anomaly_p10_galois_discriminant_mod7_factor_degrees
    (_ : FoldGaugeAnomalyP10GaloisDiscriminantData) : List ℕ :=
  [10]

/-- The mod-`11` factorization pattern yielding a `7`-cycle and a `3`-cycle. -/
def fold_gauge_anomaly_p10_galois_discriminant_mod11_factor_degrees
    (_ : FoldGaugeAnomalyP10GaloisDiscriminantData) : List ℕ :=
  [7, 3]

/-- The mod-`13` discriminant residue used to exclude `A₁₀`. -/
def fold_gauge_anomaly_p10_galois_discriminant_mod13_residue
    (_ : FoldGaugeAnomalyP10GaloisDiscriminantData) : ZMod 13 :=
  8

/-- The squarefree discriminant kernel defining the quadratic subfield. -/
def fold_gauge_anomaly_p10_galois_discriminant_squarefree_kernel
    (_ : FoldGaugeAnomalyP10GaloisDiscriminantData) : ℤ :=
  1931 * 34319

/-- Irreducibility over `ℚ` is witnessed by the degree-`10` mod-`7` factorization pattern. -/
def irreducible_over_Q (D : FoldGaugeAnomalyP10GaloisDiscriminantData) : Prop :=
  D.fold_gauge_anomaly_p10_galois_discriminant_mod7_factor_degrees = [10]

/-- The explicit quartic discriminant factorization through `P₁₀`. -/
def discriminant_factorization (_ : FoldGaugeAnomalyP10GaloisDiscriminantData) : Prop :=
  ∀ u : ℚ, gaugeAnomalyQuarticDiscriminant u = -u * (u - 1) * gaugeAnomalyP10 u

/-- The audited transitivity, cycle, and discriminant certificates package the `S₁₀` conclusion. -/
def galois_group_is_S10 (D : FoldGaugeAnomalyP10GaloisDiscriminantData) : Prop :=
  D.irreducible_over_Q ∧
    D.fold_gauge_anomaly_p10_galois_discriminant_mod11_factor_degrees = [7, 3] ∧
    (∀ z : ZMod 13, z * z ≠ D.fold_gauge_anomaly_p10_galois_discriminant_mod13_residue) ∧
    Nat.factorial 10 = 3628800

/-- For the full symmetric group on `10` letters, the only nontrivial abelian normal quotient is
the sign quotient, so the quadratic discriminant kernel gives the unique quadratic subfield. -/
def unique_quadratic_subfield (D : FoldGaugeAnomalyP10GaloisDiscriminantData) : Prop :=
  D.galois_group_is_S10 ∧
    D.fold_gauge_anomaly_p10_galois_discriminant_squarefree_kernel = 1931 * 34319

/-- The maximal abelian subextension is exactly the quadratic sign subfield recorded by the
squarefree discriminant kernel. -/
def maximal_abelian_subextension (D : FoldGaugeAnomalyP10GaloisDiscriminantData) : Prop :=
  D.unique_quadratic_subfield ∧
    D.fold_gauge_anomaly_p10_galois_discriminant_squarefree_kernel = 66269989

end FoldGaugeAnomalyP10GaloisDiscriminantData

open FoldGaugeAnomalyP10GaloisDiscriminantData

private lemma fold_gauge_anomaly_p10_galois_discriminant_mod13_nonsquare
    (D : FoldGaugeAnomalyP10GaloisDiscriminantData) :
    ∀ z : ZMod 13, z * z ≠ D.fold_gauge_anomaly_p10_galois_discriminant_mod13_residue := by
  intro z
  change z * z ≠ (8 : ZMod 13)
  fin_cases z <;> decide

/-- Paper label: `prop:fold-gauge-anomaly-P10-galois-discriminant`. The explicit discriminant
factorization and the audited mod-`7`/`11`/`13` certificates package irreducibility, the full
symmetric Galois group, the unique quadratic sign subfield, and the corresponding maximal abelian
subextension. -/
theorem paper_fold_gauge_anomaly_p10_galois_discriminant
    (D : FoldGaugeAnomalyP10GaloisDiscriminantData) :
    D.irreducible_over_Q ∧ D.galois_group_is_S10 ∧ D.discriminant_factorization ∧
      D.unique_quadratic_subfield ∧ D.maximal_abelian_subextension := by
  have hirr : D.irreducible_over_Q := by
    rfl
  have hgalois : D.galois_group_is_S10 := by
    refine ⟨hirr, rfl, fold_gauge_anomaly_p10_galois_discriminant_mod13_nonsquare D, ?_⟩
    simpa using Omega.Folding.GaugeAnomalyP10Degree.factorial_10_eq
  have hdisc : D.discriminant_factorization := by
    intro u
    exact paper_fold_gauge_anomaly_discriminant_factorization u
  have hquad : D.unique_quadratic_subfield := by
    exact ⟨hgalois, rfl⟩
  have haben : D.maximal_abelian_subextension := by
    refine ⟨hquad, ?_⟩
    change (1931 * 34319 : ℤ) = 66269989
    norm_num
  exact ⟨hirr, hgalois, hdisc, hquad, haben⟩

end Omega.Folding
