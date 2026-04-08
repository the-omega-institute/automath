import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

namespace Omega.GU

open Matrix

variable {n m : ℕ} {R : Type*} [CommRing R]

/-- If `A * M = M * B` and `v` is an eigenvector of `B`, then `M v` is an
    eigenvector of `A` with the same eigenvalue.
    thm:window6-strong-lumpability-spectral-rigidity -/
theorem eigenvector_lift_of_intertwine
    (A : Matrix (Fin n) (Fin n) R) (B : Matrix (Fin m) (Fin m) R)
    (M : Matrix (Fin n) (Fin m) R) (v : Fin m → R) (lam : R)
    (hAM : A * M = M * B) (hBv : B *ᵥ v = lam • v) :
    A *ᵥ (M *ᵥ v) = lam • (M *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, hAM, ← Matrix.mulVec_mulVec, hBv, Matrix.mulVec_smul]

/-- Spectrum inclusion via a non-trivial lifted eigenvector.
    thm:window6-strong-lumpability-spectral-rigidity -/
theorem spec_inclusion_of_intertwine
    (A : Matrix (Fin n) (Fin n) R) (B : Matrix (Fin m) (Fin m) R)
    (M : Matrix (Fin n) (Fin m) R) (v : Fin m → R) (lam : R)
    (hAM : A * M = M * B) (hBv : B *ᵥ v = lam • v)
    (hMv : M *ᵥ v ≠ 0) :
    ∃ w : Fin n → R, w ≠ 0 ∧ A *ᵥ w = lam • w :=
  ⟨M *ᵥ v, hMv, eigenvector_lift_of_intertwine A B M v lam hAM hBv⟩

/-- Rescaling the matrix rescales eigenvalues: if `(1/c) • B` has eigenvalue
    `μ` on `v`, then `B` has eigenvalue `c * μ` on `v`.
    thm:window6-strong-lumpability-spectral-rigidity -/
theorem rescale_eigenvalue {F : Type*} [Field F] {dim : ℕ}
    (B : Matrix (Fin dim) (Fin dim) F) (c : F) (hc : c ≠ 0)
    (v : Fin dim → F) (μ : F)
    (hPv : ((1 / c) • B) *ᵥ v = μ • v) :
    B *ᵥ v = (c * μ) • v := by
  have hcalc : B *ᵥ v = c • (((1 / c) • B) *ᵥ v) := by
    rw [smul_mulVec, ← smul_assoc, smul_eq_mul]
    have : c * (1 / c) = 1 := by field_simp
    rw [this, one_smul]
  rw [hcalc, hPv, smul_smul]

/-- Paper package: window-6 strong-lumpability spectral rigidity.
    thm:window6-strong-lumpability-spectral-rigidity -/
theorem paper_window6_strong_lumpability_spectral_rigidity :
    (∀ (A : Matrix (Fin n) (Fin n) R) (B : Matrix (Fin m) (Fin m) R)
       (M : Matrix (Fin n) (Fin m) R) (v : Fin m → R) (lam : R),
      A * M = M * B → B *ᵥ v = lam • v →
      A *ᵥ (M *ᵥ v) = lam • (M *ᵥ v)) ∧
    (∀ (A : Matrix (Fin n) (Fin n) R) (B : Matrix (Fin m) (Fin m) R)
       (M : Matrix (Fin n) (Fin m) R) (v : Fin m → R) (lam : R),
      A * M = M * B → B *ᵥ v = lam • v → M *ᵥ v ≠ 0 →
      ∃ w : Fin n → R, w ≠ 0 ∧ A *ᵥ w = lam • w) :=
  ⟨eigenvector_lift_of_intertwine, spec_inclusion_of_intertwine⟩

end Omega.GU
