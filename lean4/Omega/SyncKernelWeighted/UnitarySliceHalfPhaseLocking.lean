import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open scoped ComplexConjugate

noncomputable section

/-- The unit-circle twist `u = exp(i θ)`. -/
noncomputable def unitarySlicePoint (θ : ℝ) : ℂ :=
  Complex.exp (θ * Complex.I)

/-- The half-phase factor `exp(i θ / 2)`. -/
noncomputable def unitarySliceHalfPhase (θ : ℝ) : ℂ :=
  Complex.exp ((θ / 2) * Complex.I)

/-- After dividing by the half-phase, the spectrum is fixed by complex conjugation. -/
def RealNormalizedSpectrum (lam : ℂ → ℂ) : Prop :=
  ∀ θ : ℝ,
    conj (lam (unitarySlicePoint θ) / unitarySliceHalfPhase θ) =
      lam (unitarySlicePoint θ) / unitarySliceHalfPhase θ

/-- The spectral argument is locked to the half-phase modulo a real sign. -/
def ArgumentLockedModPi (lam : ℂ → ℂ) : Prop :=
  ∀ θ : ℝ, ∃ r : ℝ, lam (unitarySlicePoint θ) = unitarySliceHalfPhase θ * r

lemma conj_real_mul_I (x : ℝ) : conj ((x : ℂ) * Complex.I) = -((x : ℂ) * Complex.I) := by
  refine Complex.ext ?_ ?_ <;> simp

lemma unitarySliceHalfPhase_ne_zero (θ : ℝ) : unitarySliceHalfPhase θ ≠ 0 := by
  simp [unitarySliceHalfPhase]

lemma unitarySlicePoint_eq_halfPhase_sq (θ : ℝ) :
    unitarySlicePoint θ = unitarySliceHalfPhase θ * unitarySliceHalfPhase θ := by
  calc
    unitarySlicePoint θ = Complex.exp (2 * ((θ / 2) * Complex.I)) := by
      simp [unitarySlicePoint]
      congr 1
      ring
    _ = Complex.exp ((θ / 2) * Complex.I) ^ 2 := by
      simpa using (Complex.exp_nat_mul ((θ / 2) * Complex.I) 2)
    _ = unitarySliceHalfPhase θ * unitarySliceHalfPhase θ := by
      simp [unitarySliceHalfPhase, sq]

lemma unitarySliceHalfPhase_conj (θ : ℝ) :
    conj (unitarySliceHalfPhase θ) = (unitarySliceHalfPhase θ)⁻¹ := by
  have hdiv : (θ : ℂ) / 2 = ((θ / 2 : ℝ) : ℂ) := by
    simpa using (Complex.ofReal_div θ (2 : ℝ))
  have harg : conj ((θ : ℂ) / 2 * Complex.I) = -(((θ : ℂ) / 2) * Complex.I) := by
    rw [hdiv, show conj ((((θ / 2 : ℝ) : ℂ) * Complex.I)) = -((((θ / 2 : ℝ) : ℂ) * Complex.I)) by
      simpa using conj_real_mul_I (θ / 2)]
  calc
    conj (unitarySliceHalfPhase θ) = Complex.exp (conj (((θ : ℂ) / 2) * Complex.I)) := by
      simpa [unitarySliceHalfPhase] using (Complex.exp_conj ((θ / 2 : ℂ) * Complex.I)).symm
    _ = Complex.exp (-(((θ : ℂ) / 2) * Complex.I)) := by rw [harg]
    _ = (unitarySliceHalfPhase θ)⁻¹ := by
      simp [unitarySliceHalfPhase, Complex.exp_neg]

lemma unitarySlicePoint_inv_eq_conj (θ : ℝ) :
    (unitarySlicePoint θ)⁻¹ = conj (unitarySlicePoint θ) := by
  calc
    (unitarySlicePoint θ)⁻¹ = Complex.exp (-(θ * Complex.I)) := by
      simp [unitarySlicePoint, Complex.exp_neg]
    _ = Complex.exp (conj (θ * Complex.I)) := by rw [conj_real_mul_I θ]
    _ = conj (unitarySlicePoint θ) := by
      simpa [unitarySlicePoint] using (Complex.exp_conj (θ * Complex.I))

/-- If a spectral branch satisfies the self-duality relation `λ(u) = u λ(u⁻¹)` together with
conjugation symmetry, then on the unitary slice the normalized branch is real and its phase is
locked to `θ / 2` modulo `π`. -/
theorem paper_kernel_unitary_slice_half_phase_locking
    (lam : ℂ → ℂ)
    (hSelfDual : ∀ u : ℂ, lam u = u * lam (u⁻¹))
    (hConj : ∀ u : ℂ, lam (conj u) = conj (lam u)) :
    RealNormalizedSpectrum lam ∧ ArgumentLockedModPi lam := by
  have hreal : RealNormalizedSpectrum lam := by
    intro θ
    let u := unitarySlicePoint θ
    let p := unitarySliceHalfPhase θ
    have hp0 : p ≠ 0 := unitarySliceHalfPhase_ne_zero θ
    have huinv : u⁻¹ = conj u := by
      simpa [u] using unitarySlicePoint_inv_eq_conj θ
    have hu : u = p * p := by
      simpa [u, p] using unitarySlicePoint_eq_halfPhase_sq θ
    have hlam : lam u = u * conj (lam u) := by
      calc
        lam u = u * lam (u⁻¹) := hSelfDual u
        _ = u * lam (conj u) := by rw [huinv]
        _ = u * conj (lam u) := by rw [hConj u]
    have hnorm : lam u / p = p * conj (lam u) := by
      calc
        lam u / p = (u * conj (lam u)) / p := by
          conv_lhs => rw [hlam]
        _ = (p * p * conj (lam u)) / p := by rw [hu]
        _ = p * conj (lam u) := by
          rw [div_eq_mul_inv]
          simp [mul_assoc, mul_comm, mul_left_comm, hp0]
    calc
      conj (lam u / p) = conj (lam u) / conj p := by simp
      _ = conj (lam u) / p⁻¹ := by rw [unitarySliceHalfPhase_conj θ]
      _ = p * conj (lam u) := by
        rw [div_eq_mul_inv, inv_inv]
        simp [mul_assoc, mul_comm, mul_left_comm]
      _ = lam u / p := hnorm.symm
  refine ⟨hreal, ?_⟩
  intro θ
  let p := unitarySliceHalfPhase θ
  have hp0 : p ≠ 0 := unitarySliceHalfPhase_ne_zero θ
  have hz : conj (lam (unitarySlicePoint θ) / p) = lam (unitarySlicePoint θ) / p := hreal θ
  rcases Complex.conj_eq_iff_real.mp hz with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  calc
    lam (unitarySlicePoint θ) = (lam (unitarySlicePoint θ) / p) * p := by
      rw [div_eq_mul_inv]
      simp [mul_assoc, mul_comm, mul_left_comm, hp0]
    _ = p * r := by simpa [hr, mul_assoc, mul_comm, mul_left_comm]
    _ = unitarySliceHalfPhase θ * r := rfl

end

end Omega.SyncKernelWeighted
