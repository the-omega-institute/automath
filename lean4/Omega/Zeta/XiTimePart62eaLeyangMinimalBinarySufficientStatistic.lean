import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

namespace Omega.Zeta

set_option linter.unusedSimpArgs false

/-- The three Lee--Yang splitting types appearing in the finite binary statistic. -/
inductive xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_splitting_type
    where
  | xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_split
  | xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_single
  | xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_noroot
  deriving DecidableEq, Fintype

/-- The two binary coordinates: root/no-root and the quadratic character sign. -/
def xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_observation :
    xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_splitting_type →
      Bool × Bool
  | .xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_split => (true, true)
  | .xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_single => (true, false)
  | .xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_noroot => (false, true)

/-- The actual three-point image of the two-bit Lee--Yang observable. -/
def xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_observed_packet : Type :=
  { b : Bool × Bool //
    b = (true, true) ∨ b = (true, false) ∨ b = (false, true) }

/-- The two-bit observation, with codomain restricted to its actual three-point image. -/
def xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_packet :
    xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_splitting_type →
      xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_observed_packet
  | .xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_split =>
      ⟨(true, true), Or.inl rfl⟩
  | .xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_single =>
      ⟨(true, false), Or.inr (Or.inl rfl)⟩
  | .xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_noroot =>
      ⟨(false, true), Or.inr (Or.inr rfl)⟩

/-- A one-bit observable cannot injectively encode the three splitting types. -/
lemma xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_no_one_bit_injective
    (f : xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_splitting_type → Bool) :
    ¬ Function.Injective f := by
  intro hf
  let xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_split_state :
      xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_splitting_type :=
    .xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_split
  let xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_single_state :
      xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_splitting_type :=
    .xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_single
  let xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_noroot_state :
      xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_splitting_type :=
    .xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_noroot
  cases h_split :
      f xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_split_state <;>
    cases h_single :
      f xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_single_state <;>
    cases h_noroot :
      f xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_noroot_state
  · have h := hf (a₁ := xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_split_state)
      (a₂ := xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_single_state)
      (h_split.trans h_single.symm)
    simp [xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_split_state,
      xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_single_state,
      xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_noroot_state] at h
  · have h := hf (a₁ := xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_split_state)
      (a₂ := xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_single_state)
      (h_split.trans h_single.symm)
    simp [xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_split_state,
      xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_single_state,
      xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_noroot_state] at h
  · have h := hf (a₁ := xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_split_state)
      (a₂ := xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_noroot_state)
      (h_split.trans h_noroot.symm)
    simp [xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_split_state,
      xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_single_state,
      xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_noroot_state] at h
  · have h := hf (a₁ := xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_single_state)
      (a₂ := xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_noroot_state)
      (h_single.trans h_noroot.symm)
    simp [xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_split_state,
      xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_single_state,
      xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_noroot_state] at h
  · have h := hf (a₁ := xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_single_state)
      (a₂ := xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_noroot_state)
      (h_single.trans h_noroot.symm)
    simp [xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_split_state,
      xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_single_state,
      xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_noroot_state] at h
  · have h := hf (a₁ := xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_split_state)
      (a₂ := xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_noroot_state)
      (h_split.trans h_noroot.symm)
    simp [xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_split_state,
      xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_single_state,
      xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_noroot_state] at h
  · have h := hf (a₁ := xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_split_state)
      (a₂ := xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_single_state)
      (h_split.trans h_single.symm)
    simp [xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_split_state,
      xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_single_state,
      xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_noroot_state] at h
  · have h := hf (a₁ := xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_split_state)
      (a₂ := xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_single_state)
      (h_split.trans h_single.symm)
    simp [xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_split_state,
      xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_single_state,
      xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_noroot_state] at h

/-- Concrete statement: the two-bit packet is a bijective encoding of the three splitting types,
and no single binary coordinate can be injective on those three states. -/
def xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_statement : Prop :=
  Function.Bijective
      xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_packet ∧
    ∀ f : xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_splitting_type → Bool,
      ¬ Function.Injective f

/-- Paper label: `thm:xi-time-part62ea-leyang-minimal-binary-sufficient-statistic`. -/
theorem paper_xi_time_part62ea_leyang_minimal_binary_sufficient_statistic :
    xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_statement := by
  constructor
  · constructor
    · intro a b h
      have h_value := congrArg Subtype.val h
      cases a <;> cases b
      all_goals
        simp [xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_packet] at h_value ⊢
    · intro y
      rcases y with ⟨⟨rootBit, characterBit⟩, hy⟩
      rcases hy with hy | hy | hy
      · cases hy
        exact ⟨
          .xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_split, rfl⟩
      · cases hy
        exact ⟨
          .xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_single, rfl⟩
      · cases hy
        exact ⟨
          .xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_noroot, rfl⟩
  · exact xi_time_part62ea_leyang_minimal_binary_sufficient_statistic_no_one_bit_injective

end Omega.Zeta
