import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic
import Omega.DerivedConsequences.DerivedLeyangCubicModelsCommonQuadraticResolvent
import Omega.Zeta.XiTerminalZmStokesLeyangCommonQuadraticResolvent

namespace Omega.Conclusion

/-- The three splitting types for an `S₃` cubic. -/
inductive conclusion_leyang_stokes_quadratic_character_prime_law_split_type
  | split
  | one_plus_two
  | irreducible
  deriving DecidableEq, Repr

/-- The quadratic character is the sign of the `S₃` Frobenius permutation. -/
def conclusion_leyang_stokes_quadratic_character_prime_law_quadratic_character
    (σ : Equiv.Perm (Fin 3)) : ℤˣ :=
  σ.sign

/-- The cubic splitting type attached to an `S₃` Frobenius permutation. -/
def conclusion_leyang_stokes_quadratic_character_prime_law_split_type_of_perm
    (σ : Equiv.Perm (Fin 3)) :
    conclusion_leyang_stokes_quadratic_character_prime_law_split_type :=
  if σ = 1 then .split
  else if σ.sign = -1 then .one_plus_two else .irreducible

/-- The split permutations: only the identity. -/
def conclusion_leyang_stokes_quadratic_character_prime_law_split_set :
    Finset (Equiv.Perm (Fin 3)) :=
  Finset.univ.filter fun σ => conclusion_leyang_stokes_quadratic_character_prime_law_split_type_of_perm σ = .split

/-- The `(1+2)` permutations: exactly the transpositions. -/
def conclusion_leyang_stokes_quadratic_character_prime_law_one_plus_two_set :
    Finset (Equiv.Perm (Fin 3)) :=
  Finset.univ.filter fun σ =>
    conclusion_leyang_stokes_quadratic_character_prime_law_split_type_of_perm σ = .one_plus_two

/-- The irreducible permutations: exactly the two `3`-cycles. -/
def conclusion_leyang_stokes_quadratic_character_prime_law_irreducible_set :
    Finset (Equiv.Perm (Fin 3)) :=
  Finset.univ.filter fun σ =>
    conclusion_leyang_stokes_quadratic_character_prime_law_split_type_of_perm σ = .irreducible

/-- Natural densities obtained from class cardinalities in `S₃`. -/
noncomputable def conclusion_leyang_stokes_quadratic_character_prime_law_split_density : ℚ :=
  (conclusion_leyang_stokes_quadratic_character_prime_law_split_set.card : ℚ) / 6

noncomputable def conclusion_leyang_stokes_quadratic_character_prime_law_one_plus_two_density : ℚ :=
  (conclusion_leyang_stokes_quadratic_character_prime_law_one_plus_two_set.card : ℚ) / 6

noncomputable def conclusion_leyang_stokes_quadratic_character_prime_law_irreducible_density : ℚ :=
  (conclusion_leyang_stokes_quadratic_character_prime_law_irreducible_set.card : ℚ) / 6

lemma conclusion_leyang_stokes_quadratic_character_prime_law_split_card :
    conclusion_leyang_stokes_quadratic_character_prime_law_split_set.card = 1 := by
  native_decide

lemma conclusion_leyang_stokes_quadratic_character_prime_law_one_plus_two_card :
    conclusion_leyang_stokes_quadratic_character_prime_law_one_plus_two_set.card = 3 := by
  native_decide

lemma conclusion_leyang_stokes_quadratic_character_prime_law_irreducible_card :
    conclusion_leyang_stokes_quadratic_character_prime_law_irreducible_set.card = 2 := by
  native_decide

/-- Paper label: `thm:conclusion-leyang-stokes-quadratic-character-prime-law`. The shared Artin
and common-quadratic-resolvent packages identify the quadratic character with the sign on `S₃`;
the sign `-1` case is exactly the transposition class, while sign `+1` leaves only the identity
or a `3`-cycle; and the three densities are the corresponding class-size ratios `1/6`, `3/6`,
`2/6`. -/
theorem paper_conclusion_leyang_stokes_quadratic_character_prime_law :
    Omega.Zeta.xiTerminalStokesLeyangQuadraticResolventDiscriminant = -111 ∧
      (∀ σ : Equiv.Perm (Fin 3),
        conclusion_leyang_stokes_quadratic_character_prime_law_quadratic_character σ = -1 →
          conclusion_leyang_stokes_quadratic_character_prime_law_split_type_of_perm σ = .one_plus_two) ∧
      (∀ σ : Equiv.Perm (Fin 3),
        conclusion_leyang_stokes_quadratic_character_prime_law_quadratic_character σ = 1 →
          conclusion_leyang_stokes_quadratic_character_prime_law_split_type_of_perm σ = .split ∨
            conclusion_leyang_stokes_quadratic_character_prime_law_split_type_of_perm σ =
              .irreducible) ∧
      conclusion_leyang_stokes_quadratic_character_prime_law_split_density = (1 : ℚ) / 6 ∧
      conclusion_leyang_stokes_quadratic_character_prime_law_one_plus_two_density = (1 : ℚ) / 2 ∧
      conclusion_leyang_stokes_quadratic_character_prime_law_irreducible_density = (1 : ℚ) / 3 := by
  have hResolvent :
      Omega.Zeta.xiTerminalStokesLeyangQuadraticResolventDiscriminant = -111 := by
    exact Omega.Zeta.paper_xi_terminal_zm_stokes_leyang_common_quadratic_resolvent.2.2
  have hCommon :
      Omega.Zeta.xiTerminalStokesLeyangQuadraticResolventDiscriminant = -111 := by
    exact Omega.DerivedConsequences.paper_derived_leyang_cubic_models_common_quadratic_resolvent.2.2.2
  refine ⟨hResolvent, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ hσ
    unfold conclusion_leyang_stokes_quadratic_character_prime_law_quadratic_character at hσ
    unfold conclusion_leyang_stokes_quadratic_character_prime_law_split_type_of_perm
    by_cases hId : σ = 1
    · subst hId
      simp at hσ
    · simp [hId, hσ]
  · intro σ hσ
    unfold conclusion_leyang_stokes_quadratic_character_prime_law_quadratic_character at hσ
    unfold conclusion_leyang_stokes_quadratic_character_prime_law_split_type_of_perm
    by_cases hId : σ = 1
    · left
      simp [hId]
    · right
      simp [hId, hσ]
  · rw [conclusion_leyang_stokes_quadratic_character_prime_law_split_density,
      conclusion_leyang_stokes_quadratic_character_prime_law_split_card]
    norm_num
  · rw [conclusion_leyang_stokes_quadratic_character_prime_law_one_plus_two_density,
      conclusion_leyang_stokes_quadratic_character_prime_law_one_plus_two_card]
    norm_num
  · have : Omega.Zeta.xiTerminalStokesLeyangQuadraticResolventDiscriminant = -111 := hCommon
    rw [conclusion_leyang_stokes_quadratic_character_prime_law_irreducible_density,
      conclusion_leyang_stokes_quadratic_character_prime_law_irreducible_card]
    norm_num

end Omega.Conclusion
