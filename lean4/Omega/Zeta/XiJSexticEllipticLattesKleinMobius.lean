import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Omega.Zeta.XiJSexticEllipticLattesTMap

namespace Omega.Zeta

noncomputable section

/-- The three finite branch values of the sextic elliptic Lattès map. -/
def xi_j_sextic_elliptic_lattes_klein_mobius_e1 : ℝ := 1728

def xi_j_sextic_elliptic_lattes_klein_mobius_e2 : ℝ := -931 - 89 * Real.sqrt 89

def xi_j_sextic_elliptic_lattes_klein_mobius_e3 : ℝ := -931 + 89 * Real.sqrt 89

/-- The three Möbius involutions attached to the branch values. -/
def xi_j_sextic_elliptic_lattes_klein_mobius_phi1 (t : ℝ) : ℝ :=
  xi_j_sextic_elliptic_lattes_klein_mobius_e1 +
    ((xi_j_sextic_elliptic_lattes_klein_mobius_e1 -
          xi_j_sextic_elliptic_lattes_klein_mobius_e2) *
        (xi_j_sextic_elliptic_lattes_klein_mobius_e1 -
          xi_j_sextic_elliptic_lattes_klein_mobius_e3)) /
      (t - xi_j_sextic_elliptic_lattes_klein_mobius_e1)

def xi_j_sextic_elliptic_lattes_klein_mobius_phi2 (t : ℝ) : ℝ :=
  xi_j_sextic_elliptic_lattes_klein_mobius_e2 +
    ((xi_j_sextic_elliptic_lattes_klein_mobius_e2 -
          xi_j_sextic_elliptic_lattes_klein_mobius_e1) *
        (xi_j_sextic_elliptic_lattes_klein_mobius_e2 -
          xi_j_sextic_elliptic_lattes_klein_mobius_e3)) /
      (t - xi_j_sextic_elliptic_lattes_klein_mobius_e2)

def xi_j_sextic_elliptic_lattes_klein_mobius_phi3 (t : ℝ) : ℝ :=
  xi_j_sextic_elliptic_lattes_klein_mobius_e3 +
    ((xi_j_sextic_elliptic_lattes_klein_mobius_e3 -
          xi_j_sextic_elliptic_lattes_klein_mobius_e1) *
        (xi_j_sextic_elliptic_lattes_klein_mobius_e3 -
          xi_j_sextic_elliptic_lattes_klein_mobius_e2)) /
      (t - xi_j_sextic_elliptic_lattes_klein_mobius_e3)

/-- Concrete statement packaging the visible Klein-four Möbius relations together with the
existing rational degree-drop invariance. -/
def xi_j_sextic_elliptic_lattes_klein_mobius_statement : Prop :=
  xi_j_sextic_elliptic_lattes_klein_mobius_e1 ≠
      xi_j_sextic_elliptic_lattes_klein_mobius_e2 ∧
    xi_j_sextic_elliptic_lattes_klein_mobius_e1 ≠
      xi_j_sextic_elliptic_lattes_klein_mobius_e3 ∧
    xi_j_sextic_elliptic_lattes_klein_mobius_e2 ≠
      xi_j_sextic_elliptic_lattes_klein_mobius_e3 ∧
    (∀ t : ℝ, t ≠ xi_j_sextic_elliptic_lattes_klein_mobius_e1 →
      xi_j_sextic_elliptic_lattes_klein_mobius_phi1
          (xi_j_sextic_elliptic_lattes_klein_mobius_phi1 t) = t) ∧
    (∀ t : ℝ, t ≠ xi_j_sextic_elliptic_lattes_klein_mobius_e2 →
      xi_j_sextic_elliptic_lattes_klein_mobius_phi2
          (xi_j_sextic_elliptic_lattes_klein_mobius_phi2 t) = t) ∧
    (∀ t : ℝ, t ≠ xi_j_sextic_elliptic_lattes_klein_mobius_e3 →
      xi_j_sextic_elliptic_lattes_klein_mobius_phi3
          (xi_j_sextic_elliptic_lattes_klein_mobius_phi3 t) = t) ∧
    Fintype.card (Fin 2 × Fin 2) = 4 ∧
    (∀ t : ℚ, t ≠ 1728 → xiJDiscriminantQuadratic t ≠ 0 →
      xiJSexticInvariantPi (xiJTwoTorsionMobius t) = xiJSexticInvariantPi t ∧
        xiJSexticLattesMap (xiJTwoTorsionMobius t) = xiJSexticLattesMap t)

lemma xi_j_sextic_elliptic_lattes_klein_mobius_sqrt89_sq :
    (Real.sqrt 89) ^ 2 = (89 : ℝ) := by
  rw [Real.sq_sqrt]
  positivity

lemma xi_j_sextic_elliptic_lattes_klein_mobius_e2_ne_e3 :
    xi_j_sextic_elliptic_lattes_klein_mobius_e2 ≠
      xi_j_sextic_elliptic_lattes_klein_mobius_e3 := by
  have hsqrt89_pos : 0 < Real.sqrt 89 := by
    exact Real.sqrt_pos.2 (by norm_num)
  unfold xi_j_sextic_elliptic_lattes_klein_mobius_e2
    xi_j_sextic_elliptic_lattes_klein_mobius_e3
  linarith

lemma xi_j_sextic_elliptic_lattes_klein_mobius_e1_ne_e2 :
    xi_j_sextic_elliptic_lattes_klein_mobius_e1 ≠
      xi_j_sextic_elliptic_lattes_klein_mobius_e2 := by
  have hsqrt89_pos : 0 < Real.sqrt 89 := by
    exact Real.sqrt_pos.2 (by norm_num)
  unfold xi_j_sextic_elliptic_lattes_klein_mobius_e1
    xi_j_sextic_elliptic_lattes_klein_mobius_e2
  linarith

lemma xi_j_sextic_elliptic_lattes_klein_mobius_e1_ne_e3 :
    xi_j_sextic_elliptic_lattes_klein_mobius_e1 ≠
      xi_j_sextic_elliptic_lattes_klein_mobius_e3 := by
  have hsqrt89_lt_ten : Real.sqrt 89 < 10 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (89 : ℝ) by positivity)]
  unfold xi_j_sextic_elliptic_lattes_klein_mobius_e1
    xi_j_sextic_elliptic_lattes_klein_mobius_e3
  linarith

lemma xi_j_sextic_elliptic_lattes_klein_mobius_phi1_const :
    (xi_j_sextic_elliptic_lattes_klein_mobius_e1 -
          xi_j_sextic_elliptic_lattes_klein_mobius_e2) *
        (xi_j_sextic_elliptic_lattes_klein_mobius_e1 -
          xi_j_sextic_elliptic_lattes_klein_mobius_e3) =
      6365312 := by
  unfold xi_j_sextic_elliptic_lattes_klein_mobius_e1
    xi_j_sextic_elliptic_lattes_klein_mobius_e2
    xi_j_sextic_elliptic_lattes_klein_mobius_e3
  ring_nf
  rw [xi_j_sextic_elliptic_lattes_klein_mobius_sqrt89_sq]
  norm_num

lemma xi_j_sextic_elliptic_lattes_klein_mobius_phi1_involutive (t : ℝ)
    (ht : t ≠ xi_j_sextic_elliptic_lattes_klein_mobius_e1) :
    xi_j_sextic_elliptic_lattes_klein_mobius_phi1
        (xi_j_sextic_elliptic_lattes_klein_mobius_phi1 t) = t := by
  have ht1 : t - xi_j_sextic_elliptic_lattes_klein_mobius_e1 ≠ 0 := sub_ne_zero.mpr ht
  have hconst :
      (xi_j_sextic_elliptic_lattes_klein_mobius_e1 -
            xi_j_sextic_elliptic_lattes_klein_mobius_e2) *
          (xi_j_sextic_elliptic_lattes_klein_mobius_e1 -
            xi_j_sextic_elliptic_lattes_klein_mobius_e3) ≠
        0 := by
    rw [xi_j_sextic_elliptic_lattes_klein_mobius_phi1_const]
    norm_num
  unfold xi_j_sextic_elliptic_lattes_klein_mobius_phi1
  rw [xi_j_sextic_elliptic_lattes_klein_mobius_phi1_const]
  field_simp [ht1, hconst]
  ring_nf

lemma xi_j_sextic_elliptic_lattes_klein_mobius_phi2_involutive (t : ℝ)
    (ht : t ≠ xi_j_sextic_elliptic_lattes_klein_mobius_e2) :
    xi_j_sextic_elliptic_lattes_klein_mobius_phi2
        (xi_j_sextic_elliptic_lattes_klein_mobius_phi2 t) = t := by
  have ht2 : t - xi_j_sextic_elliptic_lattes_klein_mobius_e2 ≠ 0 := sub_ne_zero.mpr ht
  have hconst :
      ((xi_j_sextic_elliptic_lattes_klein_mobius_e2 -
              xi_j_sextic_elliptic_lattes_klein_mobius_e1) *
            (xi_j_sextic_elliptic_lattes_klein_mobius_e2 -
              xi_j_sextic_elliptic_lattes_klein_mobius_e3)) ≠
        0 := by
    refine mul_ne_zero
      (sub_ne_zero.mpr xi_j_sextic_elliptic_lattes_klein_mobius_e1_ne_e2.symm)
      (sub_ne_zero.mpr xi_j_sextic_elliptic_lattes_klein_mobius_e2_ne_e3)
  unfold xi_j_sextic_elliptic_lattes_klein_mobius_phi2
  field_simp [ht2, hconst]
  ring_nf

lemma xi_j_sextic_elliptic_lattes_klein_mobius_phi3_involutive (t : ℝ)
    (ht : t ≠ xi_j_sextic_elliptic_lattes_klein_mobius_e3) :
    xi_j_sextic_elliptic_lattes_klein_mobius_phi3
        (xi_j_sextic_elliptic_lattes_klein_mobius_phi3 t) = t := by
  have ht3 : t - xi_j_sextic_elliptic_lattes_klein_mobius_e3 ≠ 0 := sub_ne_zero.mpr ht
  have hconst :
      ((xi_j_sextic_elliptic_lattes_klein_mobius_e3 -
              xi_j_sextic_elliptic_lattes_klein_mobius_e1) *
            (xi_j_sextic_elliptic_lattes_klein_mobius_e3 -
              xi_j_sextic_elliptic_lattes_klein_mobius_e2)) ≠
        0 := by
    refine mul_ne_zero
      (sub_ne_zero.mpr xi_j_sextic_elliptic_lattes_klein_mobius_e1_ne_e3.symm)
      (sub_ne_zero.mpr xi_j_sextic_elliptic_lattes_klein_mobius_e2_ne_e3.symm)
  unfold xi_j_sextic_elliptic_lattes_klein_mobius_phi3
  field_simp [ht3, hconst]
  ring_nf

/-- Paper label: `thm:xi-j-sextic-elliptic-lattes-klein-mobius`. -/
theorem paper_xi_j_sextic_elliptic_lattes_klein_mobius :
    xi_j_sextic_elliptic_lattes_klein_mobius_statement := by
  refine ⟨xi_j_sextic_elliptic_lattes_klein_mobius_e1_ne_e2,
    xi_j_sextic_elliptic_lattes_klein_mobius_e1_ne_e3,
    xi_j_sextic_elliptic_lattes_klein_mobius_e2_ne_e3, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact xi_j_sextic_elliptic_lattes_klein_mobius_phi1_involutive t ht
  · intro t ht
    exact xi_j_sextic_elliptic_lattes_klein_mobius_phi2_involutive t ht
  · intro t ht
    exact xi_j_sextic_elliptic_lattes_klein_mobius_phi3_involutive t ht
  · native_decide
  · intro t ht hQ
    rcases paper_xi_j_sextic_elliptic_lattes_degree_drop_by_2torsion t ht hQ with
      ⟨hpi, _, hL⟩
    exact ⟨hpi, hL⟩

end

end Omega.Zeta
