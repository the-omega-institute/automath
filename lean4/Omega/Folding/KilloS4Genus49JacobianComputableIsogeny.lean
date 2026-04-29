import Mathlib.Data.List.Basic
import Mathlib.Tactic
import Omega.Folding.FoldGaugeAnomalyQuotientJacobiansIsotypic

namespace Omega.Folding

/-- The audited genus of the `D₈` quotient curve `Z`. -/
def killo_s4_genus49_jacobian_computable_isogeny_genus_z : ℕ := 4

/-- The audited genus of the ambient `S₄`-cover `𝓧`. -/
def killo_s4_genus49_jacobian_computable_isogeny_genus_x : ℕ := 49

/-- Riemann--Hurwitz for the unramified degree-`4` quotient `𝓧 → Y = 𝓧/C₄`. -/
def killo_s4_genus49_jacobian_computable_isogeny_genus_y : ℕ :=
  1 + (killo_s4_genus49_jacobian_computable_isogeny_genus_x - 1) / 4

/-- Prym dimension `dim P = g(Y) - g(Z)` for the double cover `Y → Z`. -/
def killo_s4_genus49_jacobian_computable_isogeny_prym_dimension : ℕ :=
  killo_s4_genus49_jacobian_computable_isogeny_genus_y -
    killo_s4_genus49_jacobian_computable_isogeny_genus_z

/-- Ordered dimensions of the Jacobian isotypic factors
`(J(H), J(Z), J(C_F), P)`. -/
def killo_s4_genus49_jacobian_computable_isogeny_factor_dimensions : List ℕ :=
  [5, killo_s4_genus49_jacobian_computable_isogeny_genus_z, 3,
    killo_s4_genus49_jacobian_computable_isogeny_prym_dimension]

/-- Corresponding multiplicities in the `S₄`-equivariant isogeny decomposition. -/
def killo_s4_genus49_jacobian_computable_isogeny_factor_multiplicities : List ℕ :=
  [1, 2, 3, 3]

/-- Total dimension of the genus-`49` Jacobian decomposition ledger. -/
def killo_s4_genus49_jacobian_computable_isogeny_total_dimension : ℕ :=
  5 * 1 + killo_s4_genus49_jacobian_computable_isogeny_genus_z * 2 + 3 * 3 +
    killo_s4_genus49_jacobian_computable_isogeny_prym_dimension * 3

/-- Paper label: `thm:killo-s4-genus49-jacobian-computable-isogeny`. The audited quotient genera
give `g(Z) = 4`, the unramified degree-`4` cover gives `g(Y) = 13`, hence `dim Prym(Y/Z) = 9`;
substituting these dimensions into the equivariant factorization yields the genus-`49` Jacobian
decomposition `J(H) × J(Z)^2 × J(C_F)^3 × P^3`. -/
theorem paper_killo_s4_genus49_jacobian_computable_isogeny (Q : Polynomial ℚ) :
    killo_s4_genus49_jacobian_computable_isogeny_genus_z = 4 ∧
    killo_s4_genus49_jacobian_computable_isogeny_genus_y = 13 ∧
    killo_s4_genus49_jacobian_computable_isogeny_prym_dimension = 9 ∧
    killo_s4_genus49_jacobian_computable_isogeny_factor_dimensions = [5, 4, 3, 9] ∧
    killo_s4_genus49_jacobian_computable_isogeny_factor_multiplicities = [1, 2, 3, 3] ∧
    killo_s4_genus49_jacobian_computable_isogeny_total_dimension = 49 ∧
    Nonempty
      (Omega.CircleDimension.cdim_s4_a4_quotient_is_leyang_curve_a4_quotient_point Q ≃
        Omega.CircleDimension.cdim_s4_a4_quotient_is_leyang_curve_leyang_point Q) ∧
    Omega.CircleDimension.s4v4CompatibleBiellipticPencils.card = 3 ∧
    (let D :=
        Omega.CircleDimension.cdim_s4_v4_jacobian_pullback_kernel_and_prym_splitting_prym_data;
      D.standardGeneratorExists ∧ D.invariantPolarizationsAreA2 ∧
        D.naturalPrymPolarizationIsA2) ∧
    Omega.CircleDimension.a2CartanForm.det = 3 := by
  rcases paper_fold_gauge_anomaly_quotient_jacobians_isotypic Q with
    ⟨hLeyang, hpencils, hprym, hdet⟩
  refine ⟨rfl, ?_, ?_, ?_, rfl, ?_, hLeyang, hpencils, hprym, hdet⟩
  · norm_num [killo_s4_genus49_jacobian_computable_isogeny_genus_y,
      killo_s4_genus49_jacobian_computable_isogeny_genus_x]
  · norm_num [killo_s4_genus49_jacobian_computable_isogeny_prym_dimension,
      killo_s4_genus49_jacobian_computable_isogeny_genus_y,
      killo_s4_genus49_jacobian_computable_isogeny_genus_x,
      killo_s4_genus49_jacobian_computable_isogeny_genus_z]
  · norm_num [killo_s4_genus49_jacobian_computable_isogeny_factor_dimensions,
      killo_s4_genus49_jacobian_computable_isogeny_prym_dimension,
      killo_s4_genus49_jacobian_computable_isogeny_genus_y,
      killo_s4_genus49_jacobian_computable_isogeny_genus_x,
      killo_s4_genus49_jacobian_computable_isogeny_genus_z]
  · norm_num [killo_s4_genus49_jacobian_computable_isogeny_total_dimension,
      killo_s4_genus49_jacobian_computable_isogeny_prym_dimension,
      killo_s4_genus49_jacobian_computable_isogeny_genus_y,
      killo_s4_genus49_jacobian_computable_isogeny_genus_x,
      killo_s4_genus49_jacobian_computable_isogeny_genus_z]

end Omega.Folding
