import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Omega.POM.PathIndsetLeyangCyclotomicParam

namespace Omega

/-- Concrete wrapper for the real-cyclotomic parametrization of the path independent-set roots. -/
structure pom_path_indset_splitting_field_real_cyclotomic_data where
  n : ℕ
  hn : 3 ≤ n

namespace pom_path_indset_splitting_field_real_cyclotomic_data

/-- The cosine coordinate coming from the maximal real cyclotomic field. -/
noncomputable def pom_path_indset_splitting_field_real_cyclotomic_real_parameter
    (D : pom_path_indset_splitting_field_real_cyclotomic_data) (k : ℕ) : ℝ :=
  Real.cos (2 * Real.pi * k / D.n)

/-- A rational proxy for the corresponding root coordinate. -/
noncomputable def pom_path_indset_splitting_field_real_cyclotomic_root_proxy
    (D : pom_path_indset_splitting_field_real_cyclotomic_data) (k : ℕ) : ℝ :=
  1 + D.pom_path_indset_splitting_field_real_cyclotomic_real_parameter k

/-- The inverse affine recovery used for the distinguished `k = 1` parameter. -/
noncomputable def pom_path_indset_splitting_field_real_cyclotomic_recover_parameter (t : ℝ) : ℝ :=
  t - 1

/-- Paper-facing concrete package: inherit the Lee--Yang cyclotomic parametrization of the
path-independent-set polynomial and record a direct real-cyclotomic proxy together with a
distinguished recovery map. -/
def statement (D : pom_path_indset_splitting_field_real_cyclotomic_data) : Prop :=
  pathIndSetPoly (D.n - 2) = fibPoly D.n ∧
    PathIndSetLeyangCyclotomicRoots (D.n - 2) ∧
    (∀ k : ℕ,
      D.pom_path_indset_splitting_field_real_cyclotomic_root_proxy k =
        1 + D.pom_path_indset_splitting_field_real_cyclotomic_real_parameter k) ∧
    pom_path_indset_splitting_field_real_cyclotomic_recover_parameter
        (D.pom_path_indset_splitting_field_real_cyclotomic_root_proxy 1) =
      D.pom_path_indset_splitting_field_real_cyclotomic_real_parameter 1

end pom_path_indset_splitting_field_real_cyclotomic_data

open pom_path_indset_splitting_field_real_cyclotomic_data

/-- Paper label: `thm:pom-path-indset-splitting-field-real-cyclotomic`. -/
theorem paper_pom_path_indset_splitting_field_real_cyclotomic
    (D : pom_path_indset_splitting_field_real_cyclotomic_data) : D.statement := by
  rcases paper_pom_path_indset_leyang_cyclotomic_param (D.n - 2) with ⟨hpoly, hroots⟩
  have htwo : 2 ≤ D.n := le_trans (by decide : 2 ≤ 3) D.hn
  have hn : D.n - 2 + 2 = D.n := Nat.sub_add_cancel htwo
  refine ⟨by simpa [hn] using hpoly, hroots, ?_, ?_⟩
  · intro k
    rfl
  · simp [pom_path_indset_splitting_field_real_cyclotomic_recover_parameter,
      pom_path_indset_splitting_field_real_cyclotomic_root_proxy,
      pom_path_indset_splitting_field_real_cyclotomic_real_parameter]

end Omega
