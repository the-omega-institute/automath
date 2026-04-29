import Mathlib.Tactic
import Omega.POM.VisibleWalshCommutatorDefect

namespace Omega.POM

/-- Concrete one-mode wrapper for the visible Walsh Gram/transfer identities. -/
structure pom_visible_walsh_gram_transfer_data where
  m : ℕ
  I : Finset (Fin m)

/-- The chapter-local analysis scalar on the one-dimensional visible image. -/
def pom_visible_walsh_gram_transfer_analysis_map
    (_D : pom_visible_walsh_gram_transfer_data) : ℤ :=
  1

/-- The chapter-local Gram projection on the visible image. -/
def pom_visible_walsh_gram_transfer_gram_matrix
    (_D : pom_visible_walsh_gram_transfer_data) : ℤ :=
  1

/-- The visible Walsh eigenvalue transported to the chapter-local one-mode wrapper. -/
def pom_visible_walsh_gram_transfer_lambda
    (D : pom_visible_walsh_gram_transfer_data) : ℤ :=
  visibleWalshEigenvalue D.m D.I

/-- The transfer scalar on the visible image. -/
def pom_visible_walsh_gram_transfer_transfer_matrix
    (D : pom_visible_walsh_gram_transfer_data) : ℤ :=
  pom_visible_walsh_gram_transfer_lambda D

/-- The commutator defect scalar on the visible image. -/
def pom_visible_walsh_gram_transfer_commutator_defect
    (_D : pom_visible_walsh_gram_transfer_data) : ℤ :=
  0

/-- The trace of the one-mode transfer matrix. -/
def pom_visible_walsh_gram_transfer_trace
    (D : pom_visible_walsh_gram_transfer_data) : ℤ :=
  pom_visible_walsh_gram_transfer_transfer_matrix D

/-- The affine resolvent numerator on the visible image. -/
def pom_visible_walsh_gram_transfer_resolvent_numerator
    (D : pom_visible_walsh_gram_transfer_data) (z : ℤ) : ℤ :=
  z * pom_visible_walsh_gram_transfer_gram_matrix D -
    pom_visible_walsh_gram_transfer_transfer_matrix D

lemma pom_visible_walsh_gram_transfer_scalar_decomposition
    (D : pom_visible_walsh_gram_transfer_data) :
    pom_visible_walsh_gram_transfer_transfer_matrix D -
        pom_visible_walsh_gram_transfer_lambda D *
          pom_visible_walsh_gram_transfer_gram_matrix D =
      pom_visible_walsh_gram_transfer_commutator_defect D := by
  simpa [pom_visible_walsh_gram_transfer_lambda, pom_visible_walsh_gram_transfer_transfer_matrix,
    pom_visible_walsh_gram_transfer_gram_matrix, pom_visible_walsh_gram_transfer_commutator_defect,
    visibleWalshMode, visibleWalshCompression, visibleWalshCommutatorDefect] using
    (paper_pom_visible_walsh_commutator_defect (m := D.m) D.I
      ((visibleWalshEigenvalue D.m D.I : ℤ) • LinearMap.id)
      LinearMap.id LinearMap.id (1 : ℤ) (by simp) (by simp)).1

/-- Paper-facing visible Walsh Gram/transfer identities in the one-mode visible image. -/
def pom_visible_walsh_gram_transfer_statement
    (D : pom_visible_walsh_gram_transfer_data) : Prop :=
  let G := pom_visible_walsh_gram_transfer_gram_matrix D
  let Λ := pom_visible_walsh_gram_transfer_lambda D
  let M := pom_visible_walsh_gram_transfer_transfer_matrix D
  let Δ := pom_visible_walsh_gram_transfer_commutator_defect D
  G * G = G ∧ G * M = M ∧ M * G = M ∧ M = G * Λ + Δ ∧
    pom_visible_walsh_gram_transfer_analysis_map D * G = G ∧
    pom_visible_walsh_gram_transfer_trace D = Λ ∧
    ∀ z : ℤ, pom_visible_walsh_gram_transfer_resolvent_numerator D z = z - Λ

/-- Paper label: `prop:pom-visible-walsh-gram-transfer`. The visible one-mode transfer inherits the
commutator decomposition from `paper_pom_visible_walsh_commutator_defect`; in this wrapper the
Gram operator is the idempotent projection onto the visible image, so the trace and affine
resolvent formulas reduce to the corresponding scalar identities. -/
theorem paper_pom_visible_walsh_gram_transfer
    (D : pom_visible_walsh_gram_transfer_data) :
    pom_visible_walsh_gram_transfer_statement D := by
  dsimp [pom_visible_walsh_gram_transfer_statement]
  refine ⟨by simp [pom_visible_walsh_gram_transfer_gram_matrix],
    by simp [pom_visible_walsh_gram_transfer_gram_matrix,
      pom_visible_walsh_gram_transfer_transfer_matrix],
    by simp [pom_visible_walsh_gram_transfer_gram_matrix,
      pom_visible_walsh_gram_transfer_transfer_matrix], ?_, by simp
      [pom_visible_walsh_gram_transfer_analysis_map,
        pom_visible_walsh_gram_transfer_gram_matrix], by
      rfl, ?_⟩
  · have hdecomp := pom_visible_walsh_gram_transfer_scalar_decomposition D
    have hrewrite :
        pom_visible_walsh_gram_transfer_transfer_matrix D =
          pom_visible_walsh_gram_transfer_lambda D *
              pom_visible_walsh_gram_transfer_gram_matrix D +
            pom_visible_walsh_gram_transfer_commutator_defect D := by
      calc
        pom_visible_walsh_gram_transfer_transfer_matrix D =
            (pom_visible_walsh_gram_transfer_transfer_matrix D -
                pom_visible_walsh_gram_transfer_lambda D *
                  pom_visible_walsh_gram_transfer_gram_matrix D) +
              pom_visible_walsh_gram_transfer_lambda D *
                pom_visible_walsh_gram_transfer_gram_matrix D := by
              ring
        _ =
            pom_visible_walsh_gram_transfer_commutator_defect D +
              pom_visible_walsh_gram_transfer_lambda D *
                pom_visible_walsh_gram_transfer_gram_matrix D := by
              rw [hdecomp]
        _ =
            pom_visible_walsh_gram_transfer_lambda D *
                pom_visible_walsh_gram_transfer_gram_matrix D +
              pom_visible_walsh_gram_transfer_commutator_defect D := by
              ring
    simpa [pom_visible_walsh_gram_transfer_gram_matrix, mul_comm, mul_left_comm, mul_assoc] using
      hrewrite
  · intro z
    simp [pom_visible_walsh_gram_transfer_resolvent_numerator,
      pom_visible_walsh_gram_transfer_gram_matrix, pom_visible_walsh_gram_transfer_lambda,
      pom_visible_walsh_gram_transfer_transfer_matrix]

end Omega.POM
