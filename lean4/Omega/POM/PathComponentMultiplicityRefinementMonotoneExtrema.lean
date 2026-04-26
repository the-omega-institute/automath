import Mathlib.Tactic
import Omega.Folding.FiberFusion

namespace Omega.POM

/-- The path-component multiplicity attached to a positive length profile. -/
def pom_path_component_multiplicity_refinement_monotone_extrema_weight (ls : List Nat) : Nat :=
  (ls.map (fun l => Nat.fib (l + 2))).prod

lemma pom_path_component_multiplicity_refinement_monotone_extrema_weight_pos (ls : List Nat) :
    0 < pom_path_component_multiplicity_refinement_monotone_extrema_weight ls := by
  induction ls with
  | nil =>
      simp [pom_path_component_multiplicity_refinement_monotone_extrema_weight]
  | cons a tl ih =>
      simp only [pom_path_component_multiplicity_refinement_monotone_extrema_weight,
        List.map_cons, List.prod_cons]
      exact Nat.mul_pos (Nat.fib_pos.mpr (by omega)) ih

lemma pom_path_component_multiplicity_refinement_monotone_extrema_pair_strict
    (a b : Nat) (ha : 1 <= a) (hb : 1 <= b) :
    pom_path_component_multiplicity_refinement_monotone_extrema_weight [a + b] <
      pom_path_component_multiplicity_refinement_monotone_extrema_weight [a, b] := by
  have hpair_pos : ∀ l ∈ ([a, b] : List Nat), 1 <= l := by
    intro l hl
    simp at hl
    rcases hl with rfl | rfl <;> assumption
  have hlower :=
    Omega.fib_shifted_prod_lower_bound ([a, b] : List Nat) hpair_pos
  have heq_iff :=
    Omega.paper_pom_multiplicity_lower_eq_iff ([a, b] : List Nat) hpair_pos (by simp)
  have hneq :
      pom_path_component_multiplicity_refinement_monotone_extrema_weight [a, b] ≠
        Nat.fib (([a, b] : List Nat).sum + 2) := by
    intro hEq
    have hlen : ([a, b] : List Nat).length = 1 := heq_iff.mp hEq
    simp at hlen
  have hstrict :
      Nat.fib (([a, b] : List Nat).sum + 2) <
        pom_path_component_multiplicity_refinement_monotone_extrema_weight [a, b] :=
    lt_of_le_of_ne hlower (by simpa using hneq.symm)
  simpa [pom_path_component_multiplicity_refinement_monotone_extrema_weight] using hstrict

lemma pom_path_component_multiplicity_refinement_monotone_extrema_one_step_refinement
    (pre post : List Nat) (a b : Nat) (ha : 1 <= a) (hb : 1 <= b) :
    pom_path_component_multiplicity_refinement_monotone_extrema_weight
        (pre ++ [a + b] ++ post) <
      pom_path_component_multiplicity_refinement_monotone_extrema_weight
        (pre ++ [a, b] ++ post) := by
  have hpair :=
    pom_path_component_multiplicity_refinement_monotone_extrema_pair_strict a b ha hb
  have hsuffix :
      pom_path_component_multiplicity_refinement_monotone_extrema_weight [a + b] *
          pom_path_component_multiplicity_refinement_monotone_extrema_weight post <
        pom_path_component_multiplicity_refinement_monotone_extrema_weight [a, b] *
          pom_path_component_multiplicity_refinement_monotone_extrema_weight post :=
    Nat.mul_lt_mul_of_pos_right hpair
      (pom_path_component_multiplicity_refinement_monotone_extrema_weight_pos post)
  have hprefix :
      pom_path_component_multiplicity_refinement_monotone_extrema_weight pre *
          (pom_path_component_multiplicity_refinement_monotone_extrema_weight [a + b] *
            pom_path_component_multiplicity_refinement_monotone_extrema_weight post) <
        pom_path_component_multiplicity_refinement_monotone_extrema_weight pre *
          (pom_path_component_multiplicity_refinement_monotone_extrema_weight [a, b] *
            pom_path_component_multiplicity_refinement_monotone_extrema_weight post) :=
    Nat.mul_lt_mul_of_pos_left hsuffix
      (pom_path_component_multiplicity_refinement_monotone_extrema_weight_pos pre)
  simpa [pom_path_component_multiplicity_refinement_monotone_extrema_weight, List.map_append,
    List.prod_append, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hprefix

/-- Paper label: `prop:pom-path-component-multiplicity-refinement-monotone-extrema`.
One-step refinement strictly increases the Fibonacci path-component multiplicity, and the global
extremal bounds with their equality characterizations are exactly the bounds already proved for the
shifted Fibonacci product. -/
theorem paper_pom_path_component_multiplicity_refinement_monotone_extrema :
    (∀ (pre post : List Nat) (a b : Nat), 1 <= a → 1 <= b →
      pom_path_component_multiplicity_refinement_monotone_extrema_weight
          (pre ++ [a + b] ++ post) <
        pom_path_component_multiplicity_refinement_monotone_extrema_weight
          (pre ++ [a, b] ++ post)) ∧
      ∀ ls : List Nat, (∀ l ∈ ls, 1 <= l) → ls ≠ [] →
        Nat.fib (ls.sum + 2) <=
            pom_path_component_multiplicity_refinement_monotone_extrema_weight ls ∧
          pom_path_component_multiplicity_refinement_monotone_extrema_weight ls <= 2 ^ ls.sum ∧
          (pom_path_component_multiplicity_refinement_monotone_extrema_weight ls =
              Nat.fib (ls.sum + 2) ↔
            ls.length = 1) ∧
          (pom_path_component_multiplicity_refinement_monotone_extrema_weight ls = 2 ^ ls.sum ↔
            ∀ l ∈ ls, l = 1) := by
  refine ⟨?_, ?_⟩
  · intro pre post a b ha hb
    exact
      pom_path_component_multiplicity_refinement_monotone_extrema_one_step_refinement
        pre post a b ha hb
  · intro ls hpos hne
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [pom_path_component_multiplicity_refinement_monotone_extrema_weight] using
        Omega.fib_shifted_prod_lower_bound ls hpos
    · simpa [pom_path_component_multiplicity_refinement_monotone_extrema_weight] using
        Omega.fib_shifted_prod_upper_bound ls hpos
    · simpa [pom_path_component_multiplicity_refinement_monotone_extrema_weight] using
        Omega.paper_pom_multiplicity_lower_eq_iff ls hpos hne
    · simpa [pom_path_component_multiplicity_refinement_monotone_extrema_weight] using
        Omega.paper_pom_multiplicity_upper_eq_iff ls hpos

end Omega.POM
