import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Concrete finite-congruence tomography data for one atomic surgery term. The three pairwise
coprime moduli `2, 3, 5` give a fixed CRT window of size `30`, and two positive evaluations
recover the exponent and multiplicity of the unique active coefficient. -/
structure paper_conclusion_atomic_surgery_finite_congruence_tomography_Data where
  ell : ℕ
  hEll : ell < 30
  m : ℝ
  E : ℝ
  u1 : ℝ
  u2 : ℝ
  hu1 : 0 < u1
  hu2 : 0 < u2
  hu12 : u1 ≠ u2
  hm : 0 < m

/-- The unique canonical residue class seen by the length filter modulo `q`. -/
def conclusion_atomic_surgery_finite_congruence_tomography_activeResidue
    (D : paper_conclusion_atomic_surgery_finite_congruence_tomography_Data) (q : ℕ) : ℕ :=
  D.ell % q

/-- The filtered `z^ell` coefficient at modulus `q`, residue `a`, and positive evaluation `u`. -/
noncomputable def conclusion_atomic_surgery_finite_congruence_tomography_filteredCoeff
    (D : paper_conclusion_atomic_surgery_finite_congruence_tomography_Data)
    (q a : ℕ) (u : ℝ) : ℝ :=
  if a = conclusion_atomic_surgery_finite_congruence_tomography_activeResidue D q then
    D.m * u ^ D.E
  else
    0

/-- Fixed CRT reconstruction for the pairwise coprime moduli `2, 3, 5`. -/
def conclusion_atomic_surgery_finite_congruence_tomography_crtReconstruct
    (l2 l3 l5 : ℕ) : ℕ :=
  (15 * l2 + 10 * l3 + 6 * l5) % 30

/-- Concrete theorem statement matching the finite-congruence tomography argument. -/
def paper_conclusion_atomic_surgery_finite_congruence_tomography_statement
    (D : paper_conclusion_atomic_surgery_finite_congruence_tomography_Data) : Prop :=
  (∃! a2,
      a2 < 2 ∧
        conclusion_atomic_surgery_finite_congruence_tomography_filteredCoeff D 2 a2 D.u1 ≠ 0) ∧
    (∃! a3,
      a3 < 3 ∧
        conclusion_atomic_surgery_finite_congruence_tomography_filteredCoeff D 3 a3 D.u1 ≠ 0) ∧
    (∃! a5,
      a5 < 5 ∧
        conclusion_atomic_surgery_finite_congruence_tomography_filteredCoeff D 5 a5 D.u1 ≠ 0) ∧
    conclusion_atomic_surgery_finite_congruence_tomography_crtReconstruct
        (D.ell % 2) (D.ell % 3) (D.ell % 5) = D.ell ∧
    Real.log
        (conclusion_atomic_surgery_finite_congruence_tomography_filteredCoeff D 2 (D.ell % 2) D.u2 /
          conclusion_atomic_surgery_finite_congruence_tomography_filteredCoeff D 2 (D.ell % 2) D.u1) /
      Real.log (D.u2 / D.u1) = D.E ∧
    conclusion_atomic_surgery_finite_congruence_tomography_filteredCoeff D 2 (D.ell % 2) D.u1 *
        D.u1 ^ (-D.E) =
      D.m

lemma conclusion_atomic_surgery_finite_congruence_tomography_filteredCoeff_eq
    (D : paper_conclusion_atomic_surgery_finite_congruence_tomography_Data)
    {q : ℕ} (u : ℝ) :
    conclusion_atomic_surgery_finite_congruence_tomography_filteredCoeff D q (D.ell % q) u =
      D.m * u ^ D.E := by
  simp [conclusion_atomic_surgery_finite_congruence_tomography_filteredCoeff,
    conclusion_atomic_surgery_finite_congruence_tomography_activeResidue]

lemma conclusion_atomic_surgery_finite_congruence_tomography_filteredCoeff_ne_zero
    (D : paper_conclusion_atomic_surgery_finite_congruence_tomography_Data)
    {q : ℕ} {u : ℝ} (hu : 0 < u) :
    conclusion_atomic_surgery_finite_congruence_tomography_filteredCoeff D q (D.ell % q) u ≠ 0 := by
  rw [conclusion_atomic_surgery_finite_congruence_tomography_filteredCoeff_eq D u]
  exact mul_ne_zero (ne_of_gt D.hm) (by
    exact ne_of_gt (Real.rpow_pos_of_pos hu D.E))

lemma conclusion_atomic_surgery_finite_congruence_tomography_uniqueResidue
    (D : paper_conclusion_atomic_surgery_finite_congruence_tomography_Data)
    {q : ℕ} (hq : 0 < q) {u : ℝ} (hu : 0 < u) :
    ∃! a,
      a < q ∧
        conclusion_atomic_surgery_finite_congruence_tomography_filteredCoeff D q a u ≠ 0 := by
  refine ⟨D.ell % q, ?_, ?_⟩
  · exact ⟨Nat.mod_lt _ hq, conclusion_atomic_surgery_finite_congruence_tomography_filteredCoeff_ne_zero D hu⟩
  · intro a ha
    rcases ha with ⟨_, ha_ne⟩
    by_contra hneq
    have hzero :
        conclusion_atomic_surgery_finite_congruence_tomography_filteredCoeff D q a u = 0 := by
      simp [conclusion_atomic_surgery_finite_congruence_tomography_filteredCoeff,
        conclusion_atomic_surgery_finite_congruence_tomography_activeResidue, hneq]
    exact ha_ne hzero

lemma conclusion_atomic_surgery_finite_congruence_tomography_crtReconstruct_lt
    (l2 l3 l5 : ℕ) :
    conclusion_atomic_surgery_finite_congruence_tomography_crtReconstruct l2 l3 l5 < 30 := by
  dsimp [conclusion_atomic_surgery_finite_congruence_tomography_crtReconstruct]
  exact Nat.mod_lt _ (by decide)

lemma conclusion_atomic_surgery_finite_congruence_tomography_crtReconstruct_mod_two (ell : ℕ) :
    conclusion_atomic_surgery_finite_congruence_tomography_crtReconstruct
        (ell % 2) (ell % 3) (ell % 5) ≡ ell [MOD 2] := by
  rw [Nat.ModEq, conclusion_atomic_surgery_finite_congruence_tomography_crtReconstruct]
  omega

lemma conclusion_atomic_surgery_finite_congruence_tomography_crtReconstruct_mod_three (ell : ℕ) :
    conclusion_atomic_surgery_finite_congruence_tomography_crtReconstruct
        (ell % 2) (ell % 3) (ell % 5) ≡ ell [MOD 3] := by
  rw [Nat.ModEq, conclusion_atomic_surgery_finite_congruence_tomography_crtReconstruct]
  omega

lemma conclusion_atomic_surgery_finite_congruence_tomography_crtReconstruct_mod_five (ell : ℕ) :
    conclusion_atomic_surgery_finite_congruence_tomography_crtReconstruct
        (ell % 2) (ell % 3) (ell % 5) ≡ ell [MOD 5] := by
  rw [Nat.ModEq, conclusion_atomic_surgery_finite_congruence_tomography_crtReconstruct]
  omega

lemma conclusion_atomic_surgery_finite_congruence_tomography_crtReconstruct_eq
    (D : paper_conclusion_atomic_surgery_finite_congruence_tomography_Data) :
    conclusion_atomic_surgery_finite_congruence_tomography_crtReconstruct
        (D.ell % 2) (D.ell % 3) (D.ell % 5) = D.ell := by
  have hlt :
      conclusion_atomic_surgery_finite_congruence_tomography_crtReconstruct
          (D.ell % 2) (D.ell % 3) (D.ell % 5) <
        30 :=
    conclusion_atomic_surgery_finite_congruence_tomography_crtReconstruct_lt _ _ _
  have hmod6 :
      conclusion_atomic_surgery_finite_congruence_tomography_crtReconstruct
          (D.ell % 2) (D.ell % 3) (D.ell % 5) ≡
        D.ell [MOD 2 * 3] :=
    (Nat.modEq_and_modEq_iff_modEq_mul (show Nat.Coprime 2 3 by decide)).1
      ⟨conclusion_atomic_surgery_finite_congruence_tomography_crtReconstruct_mod_two D.ell,
        conclusion_atomic_surgery_finite_congruence_tomography_crtReconstruct_mod_three D.ell⟩
  have hmod30 :
      conclusion_atomic_surgery_finite_congruence_tomography_crtReconstruct
          (D.ell % 2) (D.ell % 3) (D.ell % 5) ≡
        D.ell [MOD (2 * 3) * 5] :=
    (Nat.modEq_and_modEq_iff_modEq_mul (show Nat.Coprime (2 * 3) 5 by decide)).1
      ⟨hmod6, conclusion_atomic_surgery_finite_congruence_tomography_crtReconstruct_mod_five D.ell⟩
  have hmod30' :
      conclusion_atomic_surgery_finite_congruence_tomography_crtReconstruct
          (D.ell % 2) (D.ell % 3) (D.ell % 5) ≡
        D.ell [MOD 30] := by
    simpa using hmod30
  exact Nat.ModEq.eq_of_lt_of_lt hmod30' hlt D.hEll

lemma conclusion_atomic_surgery_finite_congruence_tomography_sliceRatio
    (D : paper_conclusion_atomic_surgery_finite_congruence_tomography_Data) :
    conclusion_atomic_surgery_finite_congruence_tomography_filteredCoeff D 2 (D.ell % 2) D.u2 /
        conclusion_atomic_surgery_finite_congruence_tomography_filteredCoeff D 2 (D.ell % 2) D.u1 =
      (D.u2 / D.u1) ^ D.E := by
  rw [conclusion_atomic_surgery_finite_congruence_tomography_filteredCoeff_eq D D.u2,
    conclusion_atomic_surgery_finite_congruence_tomography_filteredCoeff_eq D D.u1]
  rw [mul_div_mul_left _ _ (ne_of_gt D.hm)]
  exact (Real.div_rpow D.hu2.le D.hu1.le D.E).symm

/-- Paper label: `thm:conclusion-atomic-surgery-finite-congruence-tomography`. In the fixed CRT
window given by the moduli `2, 3, 5`, each filter has a unique active residue class, the three
residues recover `ell < 30`, and two positive coefficient evaluations recover the exponent `E` and
the multiplicity `m`. -/
theorem paper_conclusion_atomic_surgery_finite_congruence_tomography
    (D : paper_conclusion_atomic_surgery_finite_congruence_tomography_Data) :
    paper_conclusion_atomic_surgery_finite_congruence_tomography_statement D := by
  refine ⟨?_, ?_, ?_, conclusion_atomic_surgery_finite_congruence_tomography_crtReconstruct_eq D, ?_, ?_⟩
  · exact conclusion_atomic_surgery_finite_congruence_tomography_uniqueResidue D (by decide) D.hu1
  · exact conclusion_atomic_surgery_finite_congruence_tomography_uniqueResidue D (by decide) D.hu1
  · exact conclusion_atomic_surgery_finite_congruence_tomography_uniqueResidue D (by decide) D.hu1
  · have hratio :=
      conclusion_atomic_surgery_finite_congruence_tomography_sliceRatio D
    have hratio_pos : 0 < D.u2 / D.u1 := by
      exact div_pos D.hu2 D.hu1
    have hlog :
        Real.log
            (conclusion_atomic_surgery_finite_congruence_tomography_filteredCoeff D 2 (D.ell % 2)
                D.u2 /
              conclusion_atomic_surgery_finite_congruence_tomography_filteredCoeff D 2 (D.ell % 2)
                D.u1) =
          D.E * Real.log (D.u2 / D.u1) := by
      rw [hratio, Real.log_rpow hratio_pos]
    have hden_ne : Real.log (D.u2 / D.u1) ≠ 0 := by
      intro hzero
      have hratio_one : D.u2 / D.u1 = 1 :=
        Real.eq_one_of_pos_of_log_eq_zero hratio_pos hzero
      have hu_eq : D.u2 = D.u1 := by
        simpa using (div_eq_iff (ne_of_gt D.hu1)).mp hratio_one
      exact D.hu12 hu_eq.symm
    exact (div_eq_iff hden_ne).2 hlog
  · calc
      conclusion_atomic_surgery_finite_congruence_tomography_filteredCoeff D 2 (D.ell % 2) D.u1 *
          D.u1 ^ (-D.E) =
          D.m * (D.u1 ^ D.E * D.u1 ^ (-D.E)) := by
            rw [conclusion_atomic_surgery_finite_congruence_tomography_filteredCoeff_eq D D.u1]
            ring
      _ = D.m * (D.u1 ^ D.E * (D.u1 ^ D.E)⁻¹) := by
            rw [Real.rpow_neg D.hu1.le]
      _ = D.m := by
            have hu1E_ne : D.u1 ^ D.E ≠ 0 := by
              exact ne_of_gt (Real.rpow_pos_of_pos D.hu1 D.E)
            field_simp [hu1E_ne]

end

end Omega.Conclusion
