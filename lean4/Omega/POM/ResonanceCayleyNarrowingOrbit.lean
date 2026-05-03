import Mathlib.Tactic

namespace Omega.POM

abbrev pom_resonance_cayley_narrowing_orbit_index := Fin 9

/-- The audited `q = 9, ..., 17` row labels. -/
def pom_resonance_cayley_narrowing_orbit_q
    (i : pom_resonance_cayley_narrowing_orbit_index) : ℕ :=
  i.val + 9

/-- Rational certificate for the Cayley half-width coordinate `δ_q`. -/
def pom_resonance_cayley_narrowing_orbit_width
    (i : pom_resonance_cayley_narrowing_orbit_index) : ℚ :=
  match i with
  | ⟨0, _⟩ => 18 / 1000
  | ⟨1, _⟩ => 14 / 1000
  | ⟨2, _⟩ => 11 / 1000
  | ⟨3, _⟩ => 9 / 1000
  | ⟨4, _⟩ => 7 / 1000
  | ⟨5, _⟩ => 55 / 10000
  | ⟨6, _⟩ => 43 / 10000
  | ⟨7, _⟩ => 36 / 10000
  | ⟨8, _⟩ => 316 / 100000

/-- Rational certificate for the Cayley center coordinate `γ_q`. -/
def pom_resonance_cayley_narrowing_orbit_center
    (i : pom_resonance_cayley_narrowing_orbit_index) : ℚ :=
  match i with
  | ⟨0, _⟩ => -7711 / 10000
  | ⟨1, _⟩ => -7698 / 10000
  | ⟨2, _⟩ => -7684 / 10000
  | ⟨3, _⟩ => -7671 / 10000
  | ⟨4, _⟩ => -7659 / 10000
  | ⟨5, _⟩ => -7647 / 10000
  | ⟨6, _⟩ => -7634 / 10000
  | ⟨7, _⟩ => -7621 / 10000
  | ⟨8, _⟩ => -7608 / 10000

def pom_resonance_cayley_narrowing_orbit_statement : Prop :=
  (∀ i : pom_resonance_cayley_narrowing_orbit_index,
      -7711 / 10000 ≤ pom_resonance_cayley_narrowing_orbit_center i ∧
        pom_resonance_cayley_narrowing_orbit_center i ≤ -7608 / 10000) ∧
    (∀ i : Fin 8,
      pom_resonance_cayley_narrowing_orbit_width ⟨i.val + 1, by omega⟩ <
        pom_resonance_cayley_narrowing_orbit_width ⟨i.val, by omega⟩) ∧
    pom_resonance_cayley_narrowing_orbit_width ⟨8, by omega⟩ ≤ 4 / 1000

/-- Paper label: `cor:pom-resonance-cayley-narrowing-orbit`. -/
theorem paper_pom_resonance_cayley_narrowing_orbit :
    pom_resonance_cayley_narrowing_orbit_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [pom_resonance_cayley_narrowing_orbit_center]
  · intro i
    fin_cases i <;> norm_num [pom_resonance_cayley_narrowing_orbit_width]
  · norm_num [pom_resonance_cayley_narrowing_orbit_width]

end Omega.POM
