import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- A proper prefix witness for finite Boolean addresses. -/
def xi_address_stopping_time_equivalence_isProperPrefix (u v : List Bool) : Prop :=
  ∃ tail : List Bool, tail ≠ [] ∧ v = u ++ tail

/-- Prefix-freeness of a finite visible-address family. -/
def xi_address_stopping_time_equivalence_prefixFree (C : Finset (List Bool)) : Prop :=
  ∀ ⦃u v : List Bool⦄, u ∈ C → v ∈ C → u ≠ v →
    ¬ xi_address_stopping_time_equivalence_isProperPrefix u v

/-- A codeword is first-hit when no shorter prefix is itself visible. -/
def xi_address_stopping_time_equivalence_firstHitAtCodeword
    (C : Finset (List Bool)) (w : List Bool) : Prop :=
  w ∈ C ∧ ∀ n : ℕ, n < w.length → w.take n ∉ C

/-- Visible ξ-address families are modeled as prefix-free finite Boolean codes. -/
def xi_address_stopping_time_equivalence_XiVisibleAddressFamily
    (C : Finset (List Bool)) : Prop :=
  xi_address_stopping_time_equivalence_prefixFree C

/-- Prefix codes with stopping times are prefix-free codes whose visible words stop at first hit. -/
def xi_address_stopping_time_equivalence_XiPrefixCodeWithStoppingTimes
    (C : Finset (List Bool)) : Prop :=
  xi_address_stopping_time_equivalence_prefixFree C ∧
    ∀ w : List Bool, w ∈ C → xi_address_stopping_time_equivalence_firstHitAtCodeword C w

local notation "XiVisibleAddressFamily" =>
  xi_address_stopping_time_equivalence_XiVisibleAddressFamily

local notation "XiPrefixCodeWithStoppingTimes" =>
  xi_address_stopping_time_equivalence_XiPrefixCodeWithStoppingTimes

private lemma xi_address_stopping_time_equivalence_drop_ne_nil
    {w : List Bool} {n : ℕ} (hn : n < w.length) :
    w.drop n ≠ [] := by
  intro hdrop
  have hlen : (w.drop n).length = 0 := by simp [hdrop]
  rw [List.length_drop] at hlen
  omega

private lemma xi_address_stopping_time_equivalence_take_ne_self
    {w : List Bool} {n : ℕ} (hn : n < w.length) :
    w.take n ≠ w := by
  intro htake
  have hlen := congrArg List.length htake
  rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hn)] at hlen
  omega

/-- Paper label: `thm:xi-address-stopping-time-equivalence`. A finite visible ξ-address family is
equivalently a prefix code whose visible addresses are detected by the first-hit stopping rule. -/
theorem paper_xi_address_stopping_time_equivalence (C : Finset (List Bool)) :
    XiVisibleAddressFamily C ↔ XiPrefixCodeWithStoppingTimes C := by
  constructor
  · intro hVisible
    change xi_address_stopping_time_equivalence_prefixFree C at hVisible
    refine ⟨hVisible, ?_⟩
    intro w hw
    refine ⟨hw, ?_⟩
    intro n hn htake
    have hneq : w.take n ≠ w :=
      xi_address_stopping_time_equivalence_take_ne_self hn
    have hprefix : xi_address_stopping_time_equivalence_isProperPrefix (w.take n) w := by
      refine ⟨w.drop n, xi_address_stopping_time_equivalence_drop_ne_nil hn, ?_⟩
      exact (List.take_append_drop n w).symm
    exact hVisible htake hw hneq hprefix
  · intro hStopping
    exact hStopping.1

end Omega.Zeta
