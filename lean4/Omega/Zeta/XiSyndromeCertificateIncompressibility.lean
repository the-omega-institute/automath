import Mathlib.Tactic

namespace Omega.Zeta

universe u v

/-- Concrete certificate data for recovering a saturated shift-invariant lattice from its
monic primitive syndrome generator and for recording the associated parameter lower bound. -/
structure xi_syndrome_certificate_incompressibility_data where
  Lattice : Type u
  Polynomial : Type v
  M : Polynomial → Lattice
  generator : Lattice → Polynomial
  represents : Lattice → Polynomial → Prop
  reconstructs : Polynomial → Lattice → Prop
  degree : Polynomial → ℕ
  minParameters : Lattice → ℕ
  syndrome_injective : Function.Injective M
  represents_to_syndrome : ∀ {L : Lattice} {P : Polynomial}, represents L P → M P = L
  generator_syndrome : ∀ L : Lattice, M (generator L) = L
  reconstructs_generator : ∀ L : Lattice, reconstructs (generator L) L
  reconstructs_of_eq_generator :
    ∀ {L : Lattice} {P : Polynomial}, P = generator L → reconstructs P L
  parameter_lower_bound :
    ∀ {L : Lattice} {P : Polynomial} {d : ℕ}, represents L P → degree P = d →
      d ≤ minParameters L

/-- Paper label: `prop:xi-syndrome-certificate-incompressibility`. -/
theorem paper_xi_syndrome_certificate_incompressibility
    (D : xi_syndrome_certificate_incompressibility_data) (L : D.Lattice) (P : D.Polynomial)
    (d : ℕ) (hL : D.represents L P) (hdeg : D.degree P = d) :
    D.reconstructs P L ∧ d ≤ D.minParameters L := by
  have hP : P = D.generator L := by
    apply D.syndrome_injective
    rw [D.represents_to_syndrome hL, D.generator_syndrome L]
  exact ⟨D.reconstructs_of_eq_generator hP, D.parameter_lower_bound hL hdeg⟩

end Omega.Zeta
