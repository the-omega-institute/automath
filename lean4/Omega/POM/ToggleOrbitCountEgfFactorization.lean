import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic
import Omega.POM.ToggleOrbitCountBellProduct

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- The truncated exponential factor `E_n(u) = Σ_{k = 0}^n u^k / k!` encoded as a formal power
series in the variable `u`. -/
def pom_toggle_orbit_count_egf_factorization_component (n : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun q => if q ≤ n then (1 : ℚ) / q.factorial else 0

/-- The total truncated exponential factor obtained by multiplying the component factors. -/
def pom_toggle_orbit_count_egf_factorization_factor : List ℕ → PowerSeries ℚ
  | [] => 1
  | n :: ns =>
      pom_toggle_orbit_count_egf_factorization_component n *
        pom_toggle_orbit_count_egf_factorization_factor ns

@[simp] lemma pom_toggle_orbit_count_egf_factorization_component_coeff
    (n q : ℕ) :
    PowerSeries.coeff q (pom_toggle_orbit_count_egf_factorization_component n) =
      if q ≤ n then (1 : ℚ) / q.factorial else 0 := by
  simp [pom_toggle_orbit_count_egf_factorization_component]

lemma pom_toggle_orbit_count_egf_factorization_factor_eq_prod
    (componentSizes : List ℕ) :
    pom_toggle_orbit_count_egf_factorization_factor componentSizes =
      (componentSizes.map pom_toggle_orbit_count_egf_factorization_component).prod := by
  induction componentSizes with
  | nil =>
      simp [pom_toggle_orbit_count_egf_factorization_factor]
  | cons n ns ih =>
      simp [pom_toggle_orbit_count_egf_factorization_factor, ih]

/-- Paper label: `prop:pom-toggle-orbit-count-egf-factorization`.
The orbit-count EGF factors componentwise, while each single-component factor is the truncated
exponential series with coefficients `1 / k!` up to degree `n`. -/
theorem paper_pom_toggle_orbit_count_egf_factorization
    (componentSizes : List ℕ) :
    (∀ q : ℕ,
      toggleOrbitCount componentSizes q = (componentSizes.map (truncatedBell q)).prod) ∧
    (∀ n q : ℕ,
      PowerSeries.coeff q (pom_toggle_orbit_count_egf_factorization_component n) =
        if q ≤ n then (1 : ℚ) / q.factorial else 0) ∧
    pom_toggle_orbit_count_egf_factorization_factor componentSizes =
      (componentSizes.map pom_toggle_orbit_count_egf_factorization_component).prod := by
  exact ⟨fun q => paper_pom_toggle_orbit_count_bell_product q componentSizes,
    pom_toggle_orbit_count_egf_factorization_component_coeff,
    pom_toggle_orbit_count_egf_factorization_factor_eq_prod componentSizes⟩

end

end Omega.POM
