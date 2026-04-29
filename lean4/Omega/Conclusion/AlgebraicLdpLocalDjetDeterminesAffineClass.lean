import Omega.Conclusion.AlgebraicLDPAffineQuotientSinglevaluedness
import Omega.Conclusion.AlgebraicLdpDfiniteStokesCompression

namespace Omega.Conclusion

/-- The finite local `d`-jet of a rational jet sequence. -/
def conclusion_algebraic_ldp_local_djet_determines_affine_class_djet
    (d : ℕ) (y : ℕ → ℚ) : Fin d → ℚ :=
  fun j => y j

/-- Agreement of local `d`-jets, used as the affine quotient relation in this concrete wrapper. -/
def conclusion_algebraic_ldp_local_djet_determines_affine_class_same_djet
    (d : ℕ) (y z : ℕ → ℚ) : Prop :=
  conclusion_algebraic_ldp_local_djet_determines_affine_class_djet d y =
    conclusion_algebraic_ldp_local_djet_determines_affine_class_djet d z

/-- Concrete local determinacy statement: a positive-order recurrence compresses all higher jets
to the first `d` entries and the existing affine-quotient wrapper selects a representative whose
class is determined by that same local `d`-jet. -/
def conclusion_algebraic_ldp_local_djet_determines_affine_class_statement : Prop :=
  ∀ {d : ℕ} (_hd : 0 < d) (y : ℕ → ℚ) (a : ℕ → Fin d → ℚ),
    linearJetRecurrence d y a →
      dfiniteJetCompression d y ∧
        ∃ Q : ℕ → ℚ,
          (∀ j : Fin d, Q j = y j) ∧
            ∀ J : ℕ → ℚ,
              (∀ j : Fin d, J j = y j) →
                conclusion_algebraic_ldp_local_djet_determines_affine_class_same_djet d Q J

/-- Paper label: `cor:conclusion-algebraic-ldp-local-djet-determines-affine-class`. -/
theorem paper_conclusion_algebraic_ldp_local_djet_determines_affine_class :
    conclusion_algebraic_ldp_local_djet_determines_affine_class_statement := by
  intro d hd y a hrec
  refine ⟨paper_conclusion_algebraic_ldp_dfinite_stokes_compression hd y a hrec, ?_⟩
  let sameAffineClass : (ℕ → ℚ) → (ℕ → ℚ) → Prop :=
    conclusion_algebraic_ldp_local_djet_determines_affine_class_same_djet d
  let isBranch : (ℕ → ℚ) → Prop := fun J => ∀ j : Fin d, J j = y j
  have hI : isBranch y := by
    intro j
    rfl
  have h_all : ∀ J, isBranch J → sameAffineClass y J := by
    intro J hJ
    ext j
    exact (hJ j).symm
  rcases
      paper_conclusion_algebraic_ldp_affine_quotient_singlevaluedness
        sameAffineClass y isBranch hI h_all with
    ⟨Q, hQ, hQ_all⟩
  refine ⟨Q, hQ, ?_⟩
  intro J hJ
  exact hQ_all J hJ

end Omega.Conclusion
