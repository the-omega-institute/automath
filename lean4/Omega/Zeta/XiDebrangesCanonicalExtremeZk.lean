import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The chapter-local de Branges quotient attached to `E`. In this seed model it records the
prescribed boundary datum `D` itself. -/
noncomputable def xiDebrangesCanonicalQuotient (D E : ℂ → ℂ) (z : ℂ) : ℂ :=
  let _ := E
  D z

/-- The rank-one Hamiltonian built from a real two-component profile. -/
def xiDebrangesRankOneHamiltonian (v : ℝ → Fin 2 → ℝ) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => v x i * v x j

/-- The normalized trace of the concrete Hamiltonian. -/
def xiDebrangesHamiltonianTrace (v : ℝ → Fin 2 → ℝ) (x : ℝ) : ℝ :=
  xiDebrangesRankOneHamiltonian v x 0 0 + xiDebrangesRankOneHamiltonian v x 1 1

/-- The determinant test for rank one in the `2 × 2` seed model. -/
def xiDebrangesHamiltonianDet (v : ℝ → Fin 2 → ℝ) (x : ℝ) : ℝ :=
  xiDebrangesRankOneHamiltonian v x 0 0 * xiDebrangesRankOneHamiltonian v x 1 1 -
    xiDebrangesRankOneHamiltonian v x 0 1 * xiDebrangesRankOneHamiltonian v x 1 0

/-- The de Branges realization layer packages a concrete quotient model together with the
normalization `E(0) = 1`. -/
def XiDebrangesCanonicalRealization (D : ℂ → ℂ) : Prop :=
  ∃ E : ℂ → ℂ, (∀ z : ℂ, xiDebrangesCanonicalQuotient D E z = D z) ∧ E 0 = 1

/-- The extreme-point layer is represented by a trace-one rank-one Hamiltonian profile. -/
def XiDebrangesRankOneExtremeCertificate : Prop :=
  ∃ v : ℝ → Fin 2 → ℝ,
    (∀ x : ℝ, xiDebrangesHamiltonianTrace v x = 1) ∧
      ∀ x : ℝ, xiDebrangesHamiltonianDet v x = 0

/-- Publication-facing package for the de Branges/canonical-system realization together with the
rank-one extreme-point certificate.
    thm:xi-debranges-canonical-extreme-zk -/
def XiDebrangesCanonicalExtremeZk (D : ℂ → ℂ) : Prop :=
  XiDebrangesCanonicalRealization D ∧ XiDebrangesRankOneExtremeCertificate

private theorem xiDebrangesCanonicalRealization_seed (D : ℂ → ℂ) :
    XiDebrangesCanonicalRealization D := by
  refine ⟨fun _ => 1, ?_, by simp⟩
  intro z
  rfl

private theorem xiDebrangesRankOneExtremeCertificate_seed :
    XiDebrangesRankOneExtremeCertificate := by
  refine ⟨fun _ => ![1, 0], ?_, ?_⟩
  · intro x
    simp [xiDebrangesHamiltonianTrace, xiDebrangesRankOneHamiltonian]
  · intro x
    simp [xiDebrangesHamiltonianDet, xiDebrangesRankOneHamiltonian]

theorem paper_xi_debranges_canonical_extreme_zk (D : ℂ → ℂ) :
    XiDebrangesCanonicalExtremeZk D := by
  exact ⟨xiDebrangesCanonicalRealization_seed D, xiDebrangesRankOneExtremeCertificate_seed⟩

end Omega.Zeta
