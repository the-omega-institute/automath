import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Complex
open scoped BigOperators

/-- Concrete finite pole data for the xi-basepoint scan tomography package. -/
structure XiBasepointScanPoleDatum where
  kappa : Nat
  gamma : Fin kappa → ℝ
  delta : Fin kappa → ℝ
  kappa_pos : 0 < kappa
  delta_pos : ∀ k, 0 < delta k

namespace XiBasepointScanPoleDatum

/-- The shifted Poisson scale `a_k = 1 + δ_k`. -/
def scale (D : XiBasepointScanPoleDatum) (k : Fin D.kappa) : ℝ :=
  1 + D.delta k

/-- Positive coefficient in the Herglotz partial-fraction term. -/
noncomputable def weight (D : XiBasepointScanPoleDatum) (k : Fin D.kappa) : ℝ :=
  4 * D.delta k / D.scale k

/-- Pole location `γ_k - i a_k` in the lower half-plane. -/
noncomputable def pole (D : XiBasepointScanPoleDatum) (k : Fin D.kappa) : ℂ :=
  (D.gamma k : ℂ) - Complex.I * (D.scale k : ℂ)

/-- Residue `-4 δ_k / a_k` in the paper's partial-fraction convention. -/
noncomputable def residue (D : XiBasepointScanPoleDatum) (k : Fin D.kappa) : ℂ :=
  -((D.weight k : ℝ) : ℂ)

/-- One shifted Cauchy kernel term of the rational Herglotz transform. -/
noncomputable def herglotzTerm (D : XiBasepointScanPoleDatum) (k : Fin D.kappa) (z : ℂ) : ℂ :=
  ((D.weight k : ℝ) : ℂ) / (D.pole k - z)

/-- The finite rational Herglotz transform attached to the scan profile. -/
noncomputable def herglotz (D : XiBasepointScanPoleDatum) (z : ℂ) : ℂ :=
  ∑ k, D.herglotzTerm k z

/-- Boundary scan profile `H(x) = Σ 4δ_k / ((x-γ_k)^2 + a_k^2)`. -/
noncomputable def scanProfile (D : XiBasepointScanPoleDatum) (x : ℝ) : ℝ :=
  ∑ k, 4 * D.delta k / ((x - D.gamma k) ^ 2 + (D.scale k) ^ 2)

/-- Concrete package for the rational Herglotz representation and explicit pole tomography. -/
def rationalHerglotzPoleTomography (D : XiBasepointScanPoleDatum) : Prop :=
  (∀ z : ℂ, 0 < z.im → 0 < (D.herglotz z).im) ∧
    (∀ x : ℝ, (D.herglotz x).im = D.scanProfile x) ∧
    (∀ G : ℂ → ℂ,
      (∀ z, G z = ∑ k, D.residue k / (z - D.pole k)) →
        G = fun z => ∑ k, D.residue k / (z - D.pole k)) ∧
    (∀ k z, D.herglotzTerm k z = D.residue k / (z - D.pole k))

lemma scale_pos (D : XiBasepointScanPoleDatum) (k : Fin D.kappa) : 0 < D.scale k := by
  unfold scale
  linarith [D.delta_pos k]

lemma weight_pos (D : XiBasepointScanPoleDatum) (k : Fin D.kappa) : 0 < D.weight k := by
  unfold weight
  exact div_pos (by nlinarith [D.delta_pos k]) (D.scale_pos k)

private lemma pole_sub_ne_zero (D : XiBasepointScanPoleDatum) (k : Fin D.kappa) {z : ℂ}
    (hz : 0 < z.im) :
    D.pole k - z ≠ 0 := by
  intro h
  have him : (D.pole k - z).im = 0 := by simp [h]
  simp [pole, scale, Complex.sub_im] at him
  linarith [D.delta_pos k, hz]

private lemma shifted_atom_im_pos (w t a : ℝ) (hw : 0 < w) (ha : 0 < a) {z : ℂ}
    (hz : 0 < z.im) :
    0 < Complex.im (((w : ℂ) / (((t : ℂ) - Complex.I * (a : ℂ)) - z)) : ℂ) := by
  have hz_ne : (((t : ℂ) - Complex.I * (a : ℂ)) - z) ≠ 0 := by
    intro h
    have him : ((((t : ℂ) - Complex.I * (a : ℂ)) - z).im) = 0 := by simp [h]
    simp [Complex.sub_im] at him
    linarith
  have hnorm : 0 < Complex.normSq (((t : ℂ) - Complex.I * (a : ℂ)) - z) := Complex.normSq_pos.2 hz_ne
  have him :
      Complex.im (((w : ℂ) / (((t : ℂ) - Complex.I * (a : ℂ)) - z) : ℂ)) =
        w * (a + z.im) / Complex.normSq (((t : ℂ) - Complex.I * (a : ℂ)) - z) := by
    rw [Complex.div_im]
    simp [Complex.sub_re, Complex.sub_im]
    ring_nf
  rw [him]
  exact div_pos (mul_pos hw (by linarith)) hnorm

private lemma shifted_atom_im_of_real (w t a x : ℝ) (_ha : 0 < a) :
    Complex.im (((w : ℂ) / (((t : ℂ) - Complex.I * (a : ℂ)) - (x : ℂ)) : ℂ)) =
      w * a / ((x - t) ^ 2 + a ^ 2) := by
  have hnorm :
      Complex.normSq (((t : ℂ) - Complex.I * (a : ℂ)) - (x : ℂ)) = (x - t) ^ 2 + a ^ 2 := by
    simp [Complex.normSq, sq]
    ring
  have him :
      Complex.im (((w : ℂ) / (((t : ℂ) - Complex.I * (a : ℂ)) - (x : ℂ)) : ℂ)) =
        w * a / Complex.normSq (((t : ℂ) - Complex.I * (a : ℂ)) - (x : ℂ)) := by
    rw [Complex.div_im]
    simp [Complex.sub_re, Complex.sub_im]
    ring_nf
  rw [him, hnorm]

private lemma herglotzTerm_im_pos (D : XiBasepointScanPoleDatum) (k : Fin D.kappa) {z : ℂ}
    (hz : 0 < z.im) :
    0 < (D.herglotzTerm k z).im := by
  simpa [herglotzTerm, pole] using
    shifted_atom_im_pos (D.weight k) (D.gamma k) (D.scale k) (D.weight_pos k) (D.scale_pos k) hz

private lemma herglotzTerm_im_of_real (D : XiBasepointScanPoleDatum) (k : Fin D.kappa) (x : ℝ) :
    (D.herglotzTerm k x).im = 4 * D.delta k / ((x - D.gamma k) ^ 2 + (D.scale k) ^ 2) := by
  have hscale_ne : (D.scale k : ℝ) ≠ 0 := ne_of_gt (D.scale_pos k)
  have hw : D.weight k * D.scale k = 4 * D.delta k := by
    unfold weight
    field_simp [hscale_ne]
  rw [show 4 * D.delta k / ((x - D.gamma k) ^ 2 + (D.scale k) ^ 2) =
      (D.weight k * D.scale k) / ((x - D.gamma k) ^ 2 + (D.scale k) ^ 2) by rw [hw]]
  simpa [herglotzTerm, pole] using
    shifted_atom_im_of_real (D.weight k) (D.gamma k) (D.scale k) x (D.scale_pos k)

/-- Starting from the explicit finite sum of shifted Cauchy kernels, the rational transform
`F(z) = -Σ (4δ_k / a_k) / (z - (γ_k - i a_k))` is Herglotz on the upper half-plane, its boundary
imaginary part recovers the scan profile, and the explicit pole/residue expansion is unique by
function extensionality for that candidate.
    thm:xi-basepoint-scan-rational-herglotz-pole-tomography -/
theorem paper_xi_basepoint_scan_rational_herglotz_pole_tomography
    (D : XiBasepointScanPoleDatum) :
    D.rationalHerglotzPoleTomography := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    let k0 : Fin D.kappa := ⟨0, D.kappa_pos⟩
    have hk0 : 0 < (D.herglotzTerm k0 z).im := D.herglotzTerm_im_pos k0 hz
    have hle : (D.herglotzTerm k0 z).im ≤ ∑ k, (D.herglotzTerm k z).im := by
      simpa using
        Finset.single_le_sum
          (fun k _hk => le_of_lt (D.herglotzTerm_im_pos k hz))
          (Finset.mem_univ k0)
    have him : (D.herglotz z).im = ∑ k, (D.herglotzTerm k z).im := by
      simp [herglotz]
    calc
      0 < (D.herglotzTerm k0 z).im := hk0
      _ ≤ ∑ k, (D.herglotzTerm k z).im := hle
      _ = (D.herglotz z).im := him.symm
  · intro x
    simp [herglotz, scanProfile, D.herglotzTerm_im_of_real]
  · intro G hG
    funext z
    exact hG z
  · intro k z
    have hinv : (D.pole k - z)⁻¹ = -((z - D.pole k)⁻¹) := by
      rw [show D.pole k - z = -(z - D.pole k) by ring, inv_neg]
    calc
      D.herglotzTerm k z = ((D.weight k : ℂ)) * (D.pole k - z)⁻¹ := by
        rw [herglotzTerm, div_eq_mul_inv]
      _ = (-((D.weight k : ℂ))) * (z - D.pole k)⁻¹ := by
        rw [hinv]
        rw [mul_neg, neg_mul]
      _ = D.residue k / (z - D.pole k) := by
        rw [residue, div_eq_mul_inv]

end XiBasepointScanPoleDatum

end Omega.Zeta
