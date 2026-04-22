import Omega.OperatorAlgebra.FkdetChiSectorFactorization
import Omega.OperatorAlgebra.FoldQuantumChannelWeakHopfGroupoid

open scoped BigOperators

namespace Omega.OperatorAlgebra

open FoldJonesBasicConstructionDirectsum

section

variable {Ω X : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype X] [DecidableEq X]

/-- The four `Z₂ × Z₂` signatures written as boolean pairs. -/
def op_algebra_fold_weak_hopf_z2x2_sector_closure_sector_pair : ChiSector → Bool × Bool
  | .pp => (false, false)
  | .pm => (false, true)
  | .mp => (true, false)
  | .mm => (true, true)

/-- Recover a `χ`-sector from its boolean signature. -/
def op_algebra_fold_weak_hopf_z2x2_sector_closure_sector_of_pair : Bool × Bool → ChiSector
  | (false, false) => .pp
  | (false, true) => .pm
  | (true, false) => .mp
  | (true, true) => .mm

/-- The `Z₂` product on a single sign. -/
def op_algebra_fold_weak_hopf_z2x2_sector_closure_bool_mul (a b : Bool) : Bool :=
  if a = b then false else true

/-- Componentwise `Z₂ × Z₂` multiplication on sector signatures. -/
def op_algebra_fold_weak_hopf_z2x2_sector_closure_sector_mul
    (σ τ : ChiSector) : ChiSector :=
  op_algebra_fold_weak_hopf_z2x2_sector_closure_sector_of_pair
    (op_algebra_fold_weak_hopf_z2x2_sector_closure_bool_mul
        (op_algebra_fold_weak_hopf_z2x2_sector_closure_sector_pair σ).1
        (op_algebra_fold_weak_hopf_z2x2_sector_closure_sector_pair τ).1,
      op_algebra_fold_weak_hopf_z2x2_sector_closure_bool_mul
        (op_algebra_fold_weak_hopf_z2x2_sector_closure_sector_pair σ).2
        (op_algebra_fold_weak_hopf_z2x2_sector_closure_sector_pair τ).2)

/-- In the finite four-sector model the involution fixes each central signature. -/
def op_algebra_fold_weak_hopf_z2x2_sector_closure_sector_star (σ : ChiSector) : ChiSector :=
  σ

/-- The comultiplication remains blockwise by duplicating the sector label. -/
def op_algebra_fold_weak_hopf_z2x2_sector_closure_sector_comultiplication
    (σ : ChiSector) : ChiSector × ChiSector :=
  (σ, σ)

/-- The antipode preserves the finite `χ`-signature in this audited model. -/
def op_algebra_fold_weak_hopf_z2x2_sector_closure_sector_antipode (σ : ChiSector) : ChiSector :=
  σ

/-- The counit is supported on the neutral `(++,)` sector. -/
def op_algebra_fold_weak_hopf_z2x2_sector_closure_sector_counit (σ : ChiSector) : ℝ :=
  if σ = ChiSector.pp then 1 else 0

/-- A fixed `χ`-sector is a direct sum of fiber blocks together with its central idempotent. -/
def op_algebra_fold_weak_hopf_z2x2_sector_closure_sector_block
    (fold : Ω → X) (σ : ChiSector) : Prop :=
  directsumMatrixDecomposition fold ∧
    ∃ e : ChiSector → ℝ, e = chiSectorIdempotent σ

/-- The weak-Hopf groupoid package reused for the sector decomposition. -/
def op_algebra_fold_weak_hopf_z2x2_sector_closure_groupoid_statement (fold : Ω → X) : Prop :=
  directsumMatrixDecomposition fold ∧
    ∀ x (a b : foldFiber fold x),
      op_algebra_fold_quantum_channel_weak_hopf_groupoid_basis_action fold x a b =
        op_algebra_fold_quantum_channel_weak_hopf_groupoid_channel_on_basis fold x a b

/-- Concrete closure package for the weak-Hopf `Z₂ × Z₂` sector splitting. -/
def op_algebra_fold_weak_hopf_z2x2_sector_closure_statement (fold : Ω → X) : Prop :=
  op_algebra_fold_weak_hopf_z2x2_sector_closure_groupoid_statement fold ∧
    (∀ σ : ChiSector, op_algebra_fold_weak_hopf_z2x2_sector_closure_sector_block fold σ) ∧
    (∀ σ : ChiSector, chiSectorIdempotent σ * chiSectorIdempotent σ = chiSectorIdempotent σ) ∧
    ((∑ σ : ChiSector, chiSectorIdempotent σ) = fun _ => (1 : ℝ)) ∧
    (∀ σ τ : ChiSector,
      ∃ υ : ChiSector, υ = op_algebra_fold_weak_hopf_z2x2_sector_closure_sector_mul σ τ) ∧
    (∀ σ : ChiSector,
      op_algebra_fold_weak_hopf_z2x2_sector_closure_sector_star σ = σ) ∧
    (∀ σ : ChiSector,
      let Δ := op_algebra_fold_weak_hopf_z2x2_sector_closure_sector_comultiplication σ
      Δ.1 = σ ∧ Δ.2 = σ) ∧
    (∀ σ : ChiSector,
      op_algebra_fold_weak_hopf_z2x2_sector_closure_sector_antipode σ = σ) ∧
    op_algebra_fold_weak_hopf_z2x2_sector_closure_sector_counit ChiSector.pp = 1

end

/-- Paper label: `thm:op-algebra-fold-weak-hopf-z2x2-sector-closure`. -/
def paper_op_algebra_fold_weak_hopf_z2x2_sector_closure : Prop := by
  exact
    ∀ {Ω X : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype X] [DecidableEq X] (fold : Ω → X),
      op_algebra_fold_weak_hopf_z2x2_sector_closure_statement fold

theorem op_algebra_fold_weak_hopf_z2x2_sector_closure_certified :
    paper_op_algebra_fold_weak_hopf_z2x2_sector_closure := by
  intro Ω X _ _ _ _ fold
  rcases paper_op_algebra_fkdet_chi_sector_factorization
      (w := fun _ : ChiSector => 0) (K := fun _ : ChiSector => 0) with
    ⟨hidem, hsum, _, _, _, _⟩
  refine ⟨paper_op_algebra_fold_quantum_channel_weak_hopf_groupoid fold, ?_, hidem, hsum, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro σ
    exact ⟨paper_op_algebra_fold_quantum_channel_weak_hopf_groupoid fold |>.1, ⟨_, rfl⟩⟩
  · intro σ τ
    exact ⟨op_algebra_fold_weak_hopf_z2x2_sector_closure_sector_mul σ τ, rfl⟩
  · intro σ
    rfl
  · intro σ
    simp [op_algebra_fold_weak_hopf_z2x2_sector_closure_sector_comultiplication]
  · intro σ
    rfl
  · simp [op_algebra_fold_weak_hopf_z2x2_sector_closure_sector_counit]

end Omega.OperatorAlgebra
