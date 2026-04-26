import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete scalar determinant package for the quadratic-pencil zero criterion. -/
structure xi_qep_zero_equivalence_Data where
  L : ℂ
  s : ℂ
  z : ℂ
  B0 : ℂ
  B1 : ℂ
  xiValue : ℂ
  zRewrite : z = Complex.exp (-(s * Complex.log L))
  determinantRewrite : xiValue = z ^ (2 : ℕ) * B0 - z + L⁻¹ * B1

namespace xi_qep_zero_equivalence_Data

/-- The determinant of the one-dimensional quadratic pencil
`z^2 B_0 - z I + L^{-1} B_1`. -/
def pencilDet (D : xi_qep_zero_equivalence_Data) : ℂ :=
  D.z ^ (2 : ℕ) * D.B0 - D.z + D.L⁻¹ * D.B1

/-- The completed xi factor vanishes at the supplied spectral parameter. -/
def xi_zero (D : xi_qep_zero_equivalence_Data) : Prop :=
  D.xiValue = 0

/-- The quadratic pencil has a nonzero eigenvector in the scalar model. -/
def qep_has_nonzero_eigenvector (D : xi_qep_zero_equivalence_Data) : Prop :=
  ∃ v : ℂ, v ≠ 0 ∧ D.pencilDet * v = 0

end xi_qep_zero_equivalence_Data

/-- Paper label: `thm:xi-qep-zero-equivalence`.
Under the determinant rewrite, vanishing of the completed xi factor is equivalent to existence of a
nonzero vector in the kernel of the associated quadratic pencil. -/
theorem paper_xi_qep_zero_equivalence (D : xi_qep_zero_equivalence_Data) :
    D.xi_zero ↔ D.qep_has_nonzero_eigenvector := by
  constructor
  · intro hzero
    have hxi : D.xiValue = 0 := by
      simpa [xi_qep_zero_equivalence_Data.xi_zero] using hzero
    refine ⟨1, one_ne_zero, ?_⟩
    simp [xi_qep_zero_equivalence_Data.pencilDet, ← D.determinantRewrite, hxi]
  · rintro ⟨v, hv_ne, hker⟩
    have hpencil : D.pencilDet = 0 := by
      rcases mul_eq_zero.mp hker with hp | hv
      · exact hp
      · exact (hv_ne hv).elim
    rw [xi_qep_zero_equivalence_Data.xi_zero, D.determinantRewrite]
    simpa [xi_qep_zero_equivalence_Data.pencilDet] using hpencil

end

end Omega.Zeta
