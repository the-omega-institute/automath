import Mathlib

namespace Omega.Conclusion

/-- Torus dimension proxy attached to the free rank of a finitely generated abelian group. -/
def conclusion_relative_stokes_torus_defect_torus_dim (rank : ℕ) : ℕ := rank

/-- Quotient torus dimension computed from the ambient and image torus ranks. -/
def conclusion_relative_stokes_torus_defect_torus_quotient_dim (gRank iRank : ℕ) : ℕ :=
  gRank - iRank

/-- Relative de Rham dimension equals the torus quotient dimension in the chapter-local model. -/
def conclusion_relative_stokes_torus_defect_relative_de_rham_dim (gRank iRank : ℕ) : ℕ :=
  conclusion_relative_stokes_torus_defect_torus_quotient_dim gRank iRank

/-- Integral rank of the relative period lattice. -/
def conclusion_relative_stokes_torus_defect_integral_lattice_rank (kRank : ℕ) : ℕ := kRank

/-- Integral pairing between a relative period class and a relative cycle class. -/
def conclusion_relative_stokes_torus_defect_integral_pairing (ω γ : ℤ) : ℤ := ω * γ

/-- Concrete chapter-level package for the relative Stokes torus defect. -/
def conclusion_relative_stokes_torus_defect_statement : Prop :=
  ∀ gRank kRank iRank : ℕ,
    gRank = kRank + iRank →
      conclusion_relative_stokes_torus_defect_torus_dim gRank =
        conclusion_relative_stokes_torus_defect_torus_dim iRank +
          conclusion_relative_stokes_torus_defect_torus_dim kRank ∧
      conclusion_relative_stokes_torus_defect_torus_quotient_dim gRank iRank = kRank ∧
      conclusion_relative_stokes_torus_defect_relative_de_rham_dim gRank iRank = kRank ∧
      conclusion_relative_stokes_torus_defect_integral_lattice_rank kRank = kRank ∧
      (∀ ω₁ ω₂ γ : ℤ,
        conclusion_relative_stokes_torus_defect_integral_pairing (ω₁ + ω₂) γ =
          conclusion_relative_stokes_torus_defect_integral_pairing ω₁ γ +
            conclusion_relative_stokes_torus_defect_integral_pairing ω₂ γ) ∧
      ∀ ω γ₁ γ₂ : ℤ,
        conclusion_relative_stokes_torus_defect_integral_pairing ω (γ₁ + γ₂) =
          conclusion_relative_stokes_torus_defect_integral_pairing ω γ₁ +
            conclusion_relative_stokes_torus_defect_integral_pairing ω γ₂

/-- Paper label: `thm:conclusion-relative-stokes-torus-defect`. -/
theorem paper_conclusion_relative_stokes_torus_defect :
    conclusion_relative_stokes_torus_defect_statement := by
  intro gRank kRank iRank hExact
  refine ⟨?_, ?_, ?_, rfl, ?_, ?_⟩
  · simpa [conclusion_relative_stokes_torus_defect_torus_dim, Nat.add_comm] using hExact
  · unfold conclusion_relative_stokes_torus_defect_torus_quotient_dim
    omega
  · unfold conclusion_relative_stokes_torus_defect_relative_de_rham_dim
    unfold conclusion_relative_stokes_torus_defect_torus_quotient_dim
    omega
  · intro ω₁ ω₂ γ
    simp [conclusion_relative_stokes_torus_defect_integral_pairing, add_mul]
  · intro ω γ₁ γ₂
    simp [conclusion_relative_stokes_torus_defect_integral_pairing, mul_add]

end Omega.Conclusion
