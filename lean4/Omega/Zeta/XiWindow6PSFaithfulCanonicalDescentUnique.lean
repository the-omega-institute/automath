import Mathlib.Tactic

namespace Omega.Zeta

/-- The finite center certificate for `Z/4 × Z/2 × Z/2`. -/
abbrev xi_window6_ps_faithful_canonical_descent_unique_center :=
  Fin 4 × Bool × Bool

/-- The identity element of the finite center certificate. -/
def xi_window6_ps_faithful_canonical_descent_unique_identity :
    xi_window6_ps_faithful_canonical_descent_unique_center :=
  (0, false, false)

/-- The canonical two-torsion subgroup: first coordinate killed by multiplication by two. -/
def xi_window6_ps_faithful_canonical_descent_unique_canonical_two_torsion
    (g : xi_window6_ps_faithful_canonical_descent_unique_center) : Prop :=
  g.1.1 = 0 ∨ g.1.1 = 2

/-- A nontrivial center element supplies a canonical two-torsion witness. -/
def xi_window6_ps_faithful_canonical_descent_unique_canonical_witness
    (g : xi_window6_ps_faithful_canonical_descent_unique_center) :
    xi_window6_ps_faithful_canonical_descent_unique_center :=
  if g.1.1 % 2 = 1 then (2, false, false) else g

lemma xi_window6_ps_faithful_canonical_descent_unique_witness_mem_two_torsion
    (g : xi_window6_ps_faithful_canonical_descent_unique_center) :
    xi_window6_ps_faithful_canonical_descent_unique_canonical_two_torsion
      (xi_window6_ps_faithful_canonical_descent_unique_canonical_witness g) := by
  rcases g with ⟨a, b, c⟩
  fin_cases a <;> cases b <;> cases c <;>
    simp [xi_window6_ps_faithful_canonical_descent_unique_canonical_witness,
      xi_window6_ps_faithful_canonical_descent_unique_canonical_two_torsion]

lemma xi_window6_ps_faithful_canonical_descent_unique_witness_ne_identity
    (g : xi_window6_ps_faithful_canonical_descent_unique_center)
    (hg : g ≠ xi_window6_ps_faithful_canonical_descent_unique_identity) :
    xi_window6_ps_faithful_canonical_descent_unique_canonical_witness g ≠
      xi_window6_ps_faithful_canonical_descent_unique_identity := by
  rcases g with ⟨a, b, c⟩
  fin_cases a <;> cases b <;> cases c <;>
    simp [xi_window6_ps_faithful_canonical_descent_unique_canonical_witness,
      xi_window6_ps_faithful_canonical_descent_unique_identity] at *

/-- Kernel conditions for an injective descent through the canonical two-torsion subgroup. -/
def xi_window6_ps_faithful_canonical_descent_unique_descent_kernel_admissible
    (K : xi_window6_ps_faithful_canonical_descent_unique_center → Prop) : Prop :=
  K xi_window6_ps_faithful_canonical_descent_unique_identity ∧
    (∀ g, K g →
      K (xi_window6_ps_faithful_canonical_descent_unique_canonical_witness g)) ∧
      ∀ g, K g →
        xi_window6_ps_faithful_canonical_descent_unique_canonical_two_torsion g →
          g = xi_window6_ps_faithful_canonical_descent_unique_identity

/-- Paper-facing finite-center descent uniqueness statement. -/
def xi_window6_ps_faithful_canonical_descent_unique_statement : Prop :=
  ∀ K : xi_window6_ps_faithful_canonical_descent_unique_center → Prop,
    xi_window6_ps_faithful_canonical_descent_unique_descent_kernel_admissible K →
      ∀ g, K g → g = xi_window6_ps_faithful_canonical_descent_unique_identity

/-- Paper label: `thm:xi-window6-ps-faithful-canonical-descent-unique`. -/
theorem paper_xi_window6_ps_faithful_canonical_descent_unique :
    xi_window6_ps_faithful_canonical_descent_unique_statement := by
  intro K hK g hg
  by_cases hid : g = xi_window6_ps_faithful_canonical_descent_unique_identity
  · exact hid
  · have hWitnessK :
        K (xi_window6_ps_faithful_canonical_descent_unique_canonical_witness g) :=
      hK.2.1 g hg
    have hWitnessTwo :=
      xi_window6_ps_faithful_canonical_descent_unique_witness_mem_two_torsion g
    have hWitnessId :
        xi_window6_ps_faithful_canonical_descent_unique_canonical_witness g =
          xi_window6_ps_faithful_canonical_descent_unique_identity :=
      hK.2.2
        (xi_window6_ps_faithful_canonical_descent_unique_canonical_witness g)
        hWitnessK hWitnessTwo
    exact False.elim
      ((xi_window6_ps_faithful_canonical_descent_unique_witness_ne_identity g hid)
        hWitnessId)

end Omega.Zeta
