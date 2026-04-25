import Mathlib.Tactic

namespace Omega.CircleDimension

def killo_s4_chevalley_weil_multiplicity_49_total_dimension
    (m_triv m_sign m_v2 m_v3 m_v3' : ℕ) : ℕ :=
  m_triv + m_sign + 2 * m_v2 + 3 * m_v3 + 3 * m_v3'

def killo_s4_chevalley_weil_multiplicity_49_s4_invariants
    (m_triv _m_sign _m_v2 _m_v3 _m_v3' : ℕ) : ℕ :=
  m_triv

def killo_s4_chevalley_weil_multiplicity_49_a4_invariants
    (m_triv m_sign _m_v2 _m_v3 _m_v3' : ℕ) : ℕ :=
  m_triv + m_sign

def killo_s4_chevalley_weil_multiplicity_49_v4_invariants
    (m_triv m_sign m_v2 _m_v3 _m_v3' : ℕ) : ℕ :=
  m_triv + m_sign + 2 * m_v2

def killo_s4_chevalley_weil_multiplicity_49_s3_invariants
    (m_triv _m_sign _m_v2 m_v3 _m_v3' : ℕ) : ℕ :=
  m_triv + m_v3

def killo_s4_chevalley_weil_multiplicity_49_statement : Prop :=
  ∀ m_triv m_sign m_v2 m_v3 m_v3' : ℕ,
    killo_s4_chevalley_weil_multiplicity_49_total_dimension
        m_triv m_sign m_v2 m_v3 m_v3' = 49 →
      killo_s4_chevalley_weil_multiplicity_49_s4_invariants
          m_triv m_sign m_v2 m_v3 m_v3' = 0 →
      killo_s4_chevalley_weil_multiplicity_49_a4_invariants
          m_triv m_sign m_v2 m_v3 m_v3' = 5 →
      killo_s4_chevalley_weil_multiplicity_49_v4_invariants
          m_triv m_sign m_v2 m_v3 m_v3' = 13 →
      killo_s4_chevalley_weil_multiplicity_49_s3_invariants
          m_triv m_sign m_v2 m_v3 m_v3' = 3 →
      m_triv = 0 ∧ m_sign = 5 ∧ m_v2 = 4 ∧ m_v3 = 3 ∧ m_v3' = 9

/-- Paper label: `thm:killo-s4-chevalley-weil-multiplicity-49`.
Using the invariant dimensions for the `S₄`, `A₄`, `V₄`, and `S₃` fixed spaces together with the
total dimension `49`, the Chevalley--Weil multiplicities are uniquely recovered as
`(0, 5, 4, 3, 9)` for `(1, sgn, V₂, V₃, V₃')`. -/
theorem paper_killo_s4_chevalley_weil_multiplicity_49 :
    killo_s4_chevalley_weil_multiplicity_49_statement := by
  intro m_triv m_sign m_v2 m_v3 m_v3' hdim hs4 ha4 hv4 hs3
  have hm_triv : m_triv = 0 := by
    simpa [killo_s4_chevalley_weil_multiplicity_49_s4_invariants] using hs4
  have ha4' : m_triv + m_sign = 5 := by
    simpa [killo_s4_chevalley_weil_multiplicity_49_a4_invariants] using ha4
  have hv4' : m_triv + m_sign + 2 * m_v2 = 13 := by
    simpa [killo_s4_chevalley_weil_multiplicity_49_v4_invariants] using hv4
  have hs3' : m_triv + m_v3 = 3 := by
    simpa [killo_s4_chevalley_weil_multiplicity_49_s3_invariants] using hs3
  have hdim' : m_triv + m_sign + 2 * m_v2 + 3 * m_v3 + 3 * m_v3' = 49 := by
    simpa [killo_s4_chevalley_weil_multiplicity_49_total_dimension,
      add_assoc, add_left_comm, add_comm] using hdim
  have hm_sign : m_sign = 5 := by
    omega
  have hm_v2 : m_v2 = 4 := by
    omega
  have hm_v3 : m_v3 = 3 := by
    omega
  have hm_v3' : m_v3' = 9 := by
    omega
  exact ⟨hm_triv, hm_sign, hm_v2, hm_v3, hm_v3'⟩

end Omega.CircleDimension
