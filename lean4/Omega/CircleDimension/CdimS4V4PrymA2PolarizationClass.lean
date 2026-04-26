import Mathlib.Tactic

namespace Omega.CircleDimension

/-- A symmetric integral binary quadratic form `[[a,b],[b,c]]`. -/
structure cdim_s4_v4_prym_a2_polarization_class_form where
  a : ℤ
  b : ℤ
  c : ℤ

/-- The standard order-three action `τ = [[0,-1],[1,-1]]` on symmetric forms. -/
def cdim_s4_v4_prym_a2_polarization_class_tauTransform
    (S : cdim_s4_v4_prym_a2_polarization_class_form) :
    cdim_s4_v4_prym_a2_polarization_class_form where
  a := S.c
  b := -S.b - S.c
  c := S.a + 2 * S.b + S.c

/-- `τ`-invariance of the polarization class. -/
def cdim_s4_v4_prym_a2_polarization_class_tauInvariant
    (S : cdim_s4_v4_prym_a2_polarization_class_form) : Prop :=
  S.c = S.a ∧ -S.b - S.c = S.b ∧ S.a + 2 * S.b + S.c = S.c

/-- Determinant of the symmetric form. -/
def cdim_s4_v4_prym_a2_polarization_class_det
    (S : cdim_s4_v4_prym_a2_polarization_class_form) : ℤ :=
  S.a * S.c - S.b ^ 2

/-- Positivity for a binary symmetric form via its principal minors. -/
def cdim_s4_v4_prym_a2_polarization_class_positive
    (S : cdim_s4_v4_prym_a2_polarization_class_form) : Prop :=
  0 < S.a ∧ 0 < cdim_s4_v4_prym_a2_polarization_class_det S

/-- The `A₂` Cartan form. -/
def cdim_s4_v4_prym_a2_polarization_class_cartanForm :
    cdim_s4_v4_prym_a2_polarization_class_form where
  a := 2
  b := -1
  c := 2

/-- The polarization class singled out by `τ`-invariance, positivity, and determinant `3`. -/
def cdim_s4_v4_prym_a2_polarization_class_isPrymPolarization
    (S : cdim_s4_v4_prym_a2_polarization_class_form) : Prop :=
  cdim_s4_v4_prym_a2_polarization_class_tauInvariant S ∧
    cdim_s4_v4_prym_a2_polarization_class_positive S ∧
    cdim_s4_v4_prym_a2_polarization_class_det S = 3

/-- Solving the `τᵀ S τ = S` equation and the determinant-`3` polarization condition forces the
unique positive integral invariant form to be the `A₂` Cartan matrix.
    prop:cdim-s4-v4-prym-a2-polarization-class -/
theorem paper_cdim_s4_v4_prym_a2_polarization_class
    (S : cdim_s4_v4_prym_a2_polarization_class_form) :
    cdim_s4_v4_prym_a2_polarization_class_isPrymPolarization S ↔
      S = cdim_s4_v4_prym_a2_polarization_class_cartanForm := by
  constructor
  · intro hS
    rcases hS with ⟨hTau, hPos, hDet⟩
    rcases hTau with ⟨hca, hbb, _⟩
    have hab : S.a = -2 * S.b := by
      nlinarith [hca, hbb]
    have hcb : S.c = -2 * S.b := by
      nlinarith [hca, hab]
    have hdetb : 3 * S.b ^ 2 = 3 := by
      calc
        3 * S.b ^ 2 = (-2 * S.b) * (-2 * S.b) - S.b ^ 2 := by
          ring
        _ = S.a * S.c - S.b ^ 2 := by
          rw [hab, hcb]
        _ = 3 := hDet
    have hbSq : S.b ^ 2 = 1 := by
      nlinarith [hdetb]
    have hbneg : S.b < 0 := by
      nlinarith [hPos.1, hab]
    have hb : S.b = -1 := by
      have hfac : (S.b - 1) * (S.b + 1) = 0 := by
        nlinarith [hbSq]
      rcases eq_zero_or_eq_zero_of_mul_eq_zero hfac with hminus | hplus
      · nlinarith [hminus]
      · nlinarith [hplus, hbneg]
    have ha : S.a = 2 := by
      nlinarith [hab, hb]
    have hc : S.c = 2 := by
      nlinarith [hca, ha]
    cases S
    simp at ha hb hc
    simp [cdim_s4_v4_prym_a2_polarization_class_cartanForm, ha, hb, hc]
  · intro hS
    subst hS
    refine ⟨?_, ?_, ?_⟩
    · constructor
      · norm_num [cdim_s4_v4_prym_a2_polarization_class_cartanForm]
      · constructor <;> norm_num [cdim_s4_v4_prym_a2_polarization_class_cartanForm]
    · norm_num [cdim_s4_v4_prym_a2_polarization_class_positive,
        cdim_s4_v4_prym_a2_polarization_class_det,
        cdim_s4_v4_prym_a2_polarization_class_cartanForm]
    · norm_num [cdim_s4_v4_prym_a2_polarization_class_det,
        cdim_s4_v4_prym_a2_polarization_class_cartanForm]

end Omega.CircleDimension
