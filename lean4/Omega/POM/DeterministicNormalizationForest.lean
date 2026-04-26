import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Concrete normalization data for a terminating deterministic one-step strategy.  The
`height` witness provides the well-founded measure needed to normalize by repeatedly following the
unique chosen outgoing edge. -/
structure pom_deterministic_normalization_forest_data (α β : Type*) where
  next : α → Option α
  label : ∀ {a b}, next a = some b → β
  height : α → Nat
  decreases : ∀ {a b}, next a = some b → height b < height a

/-- The strategy subgraph keeps exactly the unique selected outgoing edge from each non-root
vertex. -/
def pom_deterministic_normalization_forest_strategy_edge {α β : Type*}
    (D : pom_deterministic_normalization_forest_data α β) (a b : α) : Prop :=
  D.next a = some b

/-- Roots of the normalization forest are precisely the vertices with no chosen outgoing edge. -/
def pom_deterministic_normalization_forest_is_normal_form {α β : Type*}
    (D : pom_deterministic_normalization_forest_data α β) (a : α) : Prop :=
  D.next a = none

/-- Fuel-bounded normalization along the deterministic strategy. -/
def pom_deterministic_normalization_forest_normalize_with_fuel {α β : Type*}
    (D : pom_deterministic_normalization_forest_data α β) : Nat → α → α
  | 0, a => a
  | n + 1, a =>
      match D.next a with
      | none => a
      | some b => pom_deterministic_normalization_forest_normalize_with_fuel D n b

/-- Full normalization obtained by spending exactly the available well-founded height. -/
def pom_deterministic_normalization_forest_normalize {α β : Type*}
    (D : pom_deterministic_normalization_forest_data α β) (a : α) : α :=
  pom_deterministic_normalization_forest_normalize_with_fuel D (D.height a) a

/-- Fuel-bounded list of edge labels encountered along the deterministic normalization path. -/
def pom_deterministic_normalization_forest_labels_with_fuel {α β : Type*}
    (D : pom_deterministic_normalization_forest_data α β) : Nat → α → List β
  | 0, _ => []
  | n + 1, a =>
      match h : D.next a with
      | none => []
      | some b => D.label h :: pom_deterministic_normalization_forest_labels_with_fuel D n b

/-- The unique root-path label sequence in the normalization forest. -/
def pom_deterministic_normalization_forest_labels_along_path {α β : Type*}
    (D : pom_deterministic_normalization_forest_data α β) (a : α) : List β :=
  pom_deterministic_normalization_forest_labels_with_fuel D (D.height a) a

/-- Prime-register trace packaged as the label sequence along the deterministic path to the root.
-/
def pom_deterministic_normalization_forest_prime_register_trace {α β : Type*}
    (D : pom_deterministic_normalization_forest_data α β) (a : α) : List β :=
  pom_deterministic_normalization_forest_labels_along_path D a

/-- Recover the strategy by taking the unique outgoing forest edge from each non-root. -/
def pom_deterministic_normalization_forest_recovered_strategy {α β : Type*}
    (D : pom_deterministic_normalization_forest_data α β) (a : α) : Option α :=
  match h : D.next a with
  | none => none
  | some b => some b

lemma pom_deterministic_normalization_forest_height_zero_is_normal_form {α β : Type*}
    (D : pom_deterministic_normalization_forest_data α β) {a : α} (h : D.height a = 0) :
    pom_deterministic_normalization_forest_is_normal_form D a := by
  unfold pom_deterministic_normalization_forest_is_normal_form
  cases hnext : D.next a with
  | none =>
      simpa [hnext]
  | some b =>
      exfalso
      have hb : D.height b < 0 := by
        simpa [h] using D.decreases hnext
      exact Nat.not_lt_zero _ hb

lemma pom_deterministic_normalization_forest_normalize_with_fuel_is_normal_form {α β : Type*}
    (D : pom_deterministic_normalization_forest_data α β) :
    ∀ n a, D.height a ≤ n →
      pom_deterministic_normalization_forest_is_normal_form D
        (pom_deterministic_normalization_forest_normalize_with_fuel D n a) := by
  intro n
  induction n with
  | zero =>
      intro a h
      exact pom_deterministic_normalization_forest_height_zero_is_normal_form D
        (Nat.le_zero.mp h)
  | succ n ih =>
      intro a h
      cases hnext : D.next a with
      | none =>
          simp [pom_deterministic_normalization_forest_normalize_with_fuel,
            pom_deterministic_normalization_forest_is_normal_form, hnext]
      | some b =>
          have hb : D.height b ≤ n := by
            exact Nat.lt_succ_iff.mp (lt_of_lt_of_le (D.decreases hnext) h)
          simpa [pom_deterministic_normalization_forest_normalize_with_fuel, hnext] using
            ih b hb

lemma pom_deterministic_normalization_forest_normalize_is_normal_form {α β : Type*}
    (D : pom_deterministic_normalization_forest_data α β) (a : α) :
    pom_deterministic_normalization_forest_is_normal_form D
      (pom_deterministic_normalization_forest_normalize D a) := by
  exact pom_deterministic_normalization_forest_normalize_with_fuel_is_normal_form D
    (D.height a) a le_rfl

/-- Deterministic normalization strategies are exactly out-degree-one acyclic forest choices, and
the prime-register trace is the corresponding root-path label sequence.
    thm:pom-deterministic-normalization-forest -/
theorem paper_pom_deterministic_normalization_forest {α β : Type*}
    (D : pom_deterministic_normalization_forest_data α β) :
    (∀ a, pom_deterministic_normalization_forest_is_normal_form D a ∨
      ∃! b, pom_deterministic_normalization_forest_strategy_edge D a b) ∧
    (∀ a, pom_deterministic_normalization_forest_is_normal_form D
      (pom_deterministic_normalization_forest_normalize D a)) ∧
    (∀ a, pom_deterministic_normalization_forest_recovered_strategy D a = D.next a) ∧
    (∀ a, pom_deterministic_normalization_forest_prime_register_trace D a =
      pom_deterministic_normalization_forest_labels_along_path D a) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    cases hnext : D.next a with
    | none =>
        left
        simpa [pom_deterministic_normalization_forest_is_normal_form, hnext]
    | some b =>
        right
        refine ⟨b, ?_, ?_⟩
        · simpa [pom_deterministic_normalization_forest_strategy_edge, hnext]
        · intro c hc
          have hEq : some c = some b := by rw [← hc, hnext]
          exact Option.some.inj hEq
  · intro a
    exact pom_deterministic_normalization_forest_normalize_is_normal_form D a
  · intro a
    unfold pom_deterministic_normalization_forest_recovered_strategy
    cases hnext : D.next a with
    | none =>
        simp [hnext]
    | some b =>
        simp [hnext]
  · intro a
    rfl

end Omega.POM
