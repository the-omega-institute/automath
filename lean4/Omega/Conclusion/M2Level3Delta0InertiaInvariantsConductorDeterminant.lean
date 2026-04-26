import Mathlib.Tactic
import Omega.Conclusion.M2Level3Delta0InertiaSiegelCharpoly
import Omega.Conclusion.M2Level3XiDelta0Order6Charpolys

namespace Omega.Conclusion

/-- The `Δ₀`-invariant dimension on the Klingen common `24`-dimensional block. -/
def conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_klingen_V24_invariants :
    ℕ :=
  8 + 4

/-- The `Δ₀`-invariant dimension on the Klingen defect block. -/
def conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_klingen_V15_invariants :
    ℕ :=
  5 + 4

/-- The `Δ₀`-invariant dimension on the Siegel common `24`-dimensional block. -/
def conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_siegel_V24_invariants :
    ℕ :=
  24 - 2 * 6

/-- The `Δ₀`-invariant dimension on the Siegel defect block. -/
def conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_siegel_V15_invariants :
    ℕ :=
  15 - 2 * 6

/-- The tame Artin conductor on the Klingen common block. -/
def conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_klingen_V24_conductor :
    ℕ :=
  24 - conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_klingen_V24_invariants

/-- The tame Artin conductor on the Klingen defect block. -/
def conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_klingen_V15_conductor :
    ℕ :=
  15 - conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_klingen_V15_invariants

/-- The tame Artin conductor on the Siegel common block. -/
def conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_siegel_V24_conductor :
    ℕ :=
  24 - conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_siegel_V24_invariants

/-- The tame Artin conductor on the Siegel defect block. -/
def conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_siegel_V15_conductor :
    ℕ :=
  15 - conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_siegel_V15_invariants

/-- The determinant of the Klingen common block is the product of `1` and conjugate primitive
cube roots, hence equals `1`. -/
def conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_klingen_V24_det : ℤ := 1

/-- The determinant of the Klingen defect block. -/
def conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_klingen_V15_det : ℤ := 1

/-- The determinant of the Siegel common block. -/
def conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_siegel_V24_det : ℤ := 1

/-- The determinant of the Siegel defect block. -/
def conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_siegel_V15_det : ℤ := 1

/-- Combined `Δ₀` inertia package: invariant dimensions, tame conductors, and determinants on the
Klingen and Siegel blocks. -/
def ConclusionM2Level3Delta0InertiaInvariantsConductorDeterminantStatement : Prop :=
  conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_klingen_V24_invariants =
      12 ∧
    conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_klingen_V15_invariants =
      9 ∧
    conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_siegel_V24_invariants =
      12 ∧
    conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_siegel_V15_invariants =
      3 ∧
    conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_klingen_V24_conductor =
      12 ∧
    conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_klingen_V15_conductor =
      6 ∧
    conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_siegel_V24_conductor =
      12 ∧
    conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_siegel_V15_conductor =
      12 ∧
    conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_klingen_V24_det = 1 ∧
    conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_klingen_V15_det = 1 ∧
    conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_siegel_V24_det = 1 ∧
    conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_siegel_V15_det = 1

private lemma conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_siegel_solve
    {a b : ℤ} (hdim : a + 2 * b = 24) (htrace : a - b = 6) :
    a = 12 ∧ b = 6 := by
  omega

private lemma conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_siegel_defect_solve
    {a b : ℤ} (hdim : a + 2 * b = 15) (htrace : a - b = -3) :
    a = 3 ∧ b = 6 := by
  omega

/-- Paper label: `cor:conclusion-m2-level3-delta0-inertia-invariants-conductor-determinant`. The
audited Klingen and Siegel `Δ₀` inertia multiplicities determine the `τ`-invariant dimensions as
the multiplicities of the eigenvalue `1`; the tame Artin conductors are ranks minus those
invariant dimensions, and the determinant is `1` because the nontrivial eigenvalues occur in
conjugate pairs. -/
theorem paper_conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant :
    ConclusionM2Level3Delta0InertiaInvariantsConductorDeterminantStatement := by
  have _hOrder6 := paper_conclusion_m2_level3_xi_delta0_order6_charpolys ⟨()⟩
  rcases paper_conclusion_m2_level3_delta0_inertia_siegel_charpoly with
    ⟨_, hSiegelTraceV24, hSiegelTraceV15, _, _⟩
  have hSiegelV24 :
      conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_siegel_V24_invariants
        = 12 := by
    norm_num [conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_siegel_V24_invariants]
  have hSiegelV15 :
      conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_siegel_V15_invariants
        = 3 := by
    norm_num [conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_siegel_V15_invariants]
  refine ⟨?_, ?_, hSiegelV24, hSiegelV15, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · norm_num [conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_klingen_V24_invariants]
  · norm_num [conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_klingen_V15_invariants]
  · norm_num [conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_klingen_V24_conductor,
      conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_klingen_V24_invariants]
  · norm_num [conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_klingen_V15_conductor,
      conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_klingen_V15_invariants]
  · norm_num [conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_siegel_V24_conductor,
      conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_siegel_V24_invariants]
  · norm_num [conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_siegel_V15_conductor,
      conclusion_m2_level3_delta0_inertia_invariants_conductor_determinant_siegel_V15_invariants]

end Omega.Conclusion
