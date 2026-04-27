import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete Prym polarization data in dimension three.  The entries of `polarizationType`
are the elementary divisors, `polarizationDegree` is the degree of the polarization map,
and `h0Value` records the dimension of global sections. -/
structure conclusion_leyang_prym3_polarization_kernel_h0_data where
  polarizationType : Fin 3 → ℕ
  polarizationDegree : ℕ
  kernelCardinality : ℕ
  pullbackTwoTorsionCardinality : ℕ
  h0Value : ℕ

namespace conclusion_leyang_prym3_polarization_kernel_h0_data

def conclusion_leyang_prym3_polarization_kernel_h0_typeProduct
    (D : conclusion_leyang_prym3_polarization_kernel_h0_data) : ℕ :=
  D.polarizationType 0 * D.polarizationType 1 * D.polarizationType 2

/-- The standard package of facts for the Leyang Prym double cover: the elementary divisors
are positive and ordered by divisibility, their product is two, the polarization-map degree is
four, the pullback kernel is the two-torsion kernel, and Riemann-Roch gives `h0 = 2`. -/
def prym_double_cover_package
    (D : conclusion_leyang_prym3_polarization_kernel_h0_data) : Prop :=
  0 < D.polarizationType 0 ∧
    0 < D.polarizationType 1 ∧
    0 < D.polarizationType 2 ∧
    D.polarizationType 0 ∣ D.polarizationType 1 ∧
    D.polarizationType 1 ∣ D.polarizationType 2 ∧
    D.conclusion_leyang_prym3_polarization_kernel_h0_typeProduct = 2 ∧
    D.polarizationDegree = 4 ∧
    D.kernelCardinality = D.pullbackTwoTorsionCardinality ∧
    D.pullbackTwoTorsionCardinality = 4 ∧
    D.h0Value = 2

def degree_four (D : conclusion_leyang_prym3_polarization_kernel_h0_data) : Prop :=
  D.polarizationDegree = 4

def type_112 (D : conclusion_leyang_prym3_polarization_kernel_h0_data) : Prop :=
  D.polarizationType 0 = 1 ∧ D.polarizationType 1 = 1 ∧ D.polarizationType 2 = 2

def kernel_pullback_two_torsion
    (D : conclusion_leyang_prym3_polarization_kernel_h0_data) : Prop :=
  D.kernelCardinality = 4 ∧ D.kernelCardinality = D.pullbackTwoTorsionCardinality

def h0_two (D : conclusion_leyang_prym3_polarization_kernel_h0_data) : Prop :=
  D.h0Value = 2

end conclusion_leyang_prym3_polarization_kernel_h0_data

private lemma conclusion_leyang_prym3_polarization_kernel_h0_classifies_112
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a ∣ b)
    (hbc : b ∣ c) (hprod : a * b * c = 2) : a = 1 ∧ b = 1 ∧ c = 2 := by
  have ha_dvd_two : a ∣ 2 := by
    refine ⟨b * c, ?_⟩
    rw [← hprod, Nat.mul_assoc]
  have hb_dvd_two : b ∣ 2 := by
    refine ⟨a * c, ?_⟩
    rw [← hprod]
    ac_rfl
  have hc_dvd_two : c ∣ 2 := by
    refine ⟨a * b, ?_⟩
    rw [← hprod]
    ac_rfl
  have ha_le : a ≤ 2 := Nat.le_of_dvd (by norm_num) ha_dvd_two
  have hb_le : b ≤ 2 := Nat.le_of_dvd (by norm_num) hb_dvd_two
  have hc_le : c ≤ 2 := Nat.le_of_dvd (by norm_num) hc_dvd_two
  interval_cases a <;> interval_cases b <;> interval_cases c <;>
    simp_all [Nat.dvd_iff_mod_eq_zero]

/-- Paper label: `thm:conclusion-leyang-prym3-polarization-kernel-h0`. -/
theorem paper_conclusion_leyang_prym3_polarization_kernel_h0
    (D : conclusion_leyang_prym3_polarization_kernel_h0_data)
    (hprym : D.prym_double_cover_package) :
    D.degree_four ∧ D.type_112 ∧ D.kernel_pullback_two_torsion ∧ D.h0_two := by
  rcases hprym with
    ⟨h0pos, h1pos, h2pos, h01dvd, h12dvd, hprod, hdeg, hker, htwo, hh0⟩
  have htype := conclusion_leyang_prym3_polarization_kernel_h0_classifies_112
    (a := D.polarizationType 0) (b := D.polarizationType 1) (c := D.polarizationType 2)
    h0pos h1pos h2pos h01dvd h12dvd hprod
  refine ⟨hdeg, htype, ?_, hh0⟩
  exact ⟨hker.trans htwo, hker⟩

end Omega.Conclusion
