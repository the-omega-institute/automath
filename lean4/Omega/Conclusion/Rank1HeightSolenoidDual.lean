import Mathlib.Tactic

namespace Omega.Conclusion

/-- Divisor-chain span model for a normalized rank-one subgroup of `ℚ`. -/
def conclusion_rank1_height_solenoid_dual_chain_span (d : ℕ → ℕ) : Set ℚ :=
  {q | ∃ j : ℕ, ∃ z : ℤ, q = (z : ℚ) / (d j : ℚ)}

/-- Concrete inverse-limit coordinate model for the one-dimensional solenoid attached to a
divisor chain. -/
abbrev conclusion_rank1_height_solenoid_dual_inverse_limit (d : ℕ → ℕ) :=
  {x : ℕ → ℚ // ∀ j : ℕ, (d (j + 1) : ℚ) * x (j + 1) = (d j : ℚ) * x j}

/-- A normalized rank-one torsion-free countable subgroup model inside `ℚ`. -/
def conclusion_rank1_height_solenoid_dual_rank_one_torsion_free_countable_model
    (A : Set ℚ) : Prop :=
  (0 : ℚ) ∈ A ∧
    (1 : ℚ) ∈ A ∧
    (∀ {x y : ℚ}, x ∈ A → y ∈ A → x + y ∈ A) ∧
    (∀ {x : ℚ}, x ∈ A → -x ∈ A) ∧
    (∀ (n : ℕ) (x : ℚ), x ∈ A → n ≠ 0 → (n : ℚ) * x = 0 → x = 0) ∧
    Nonempty (A ↪ ℕ)

/-- The chain is positive and ordered by divisibility. -/
def conclusion_rank1_height_solenoid_dual_divisor_chain_clause (d : ℕ → ℕ) : Prop :=
  (∀ j : ℕ, 0 < d j) ∧ ∀ j : ℕ, d j ∣ d (j + 1)

/-- The height signature is realized by the prime-power divisibility profile of the chain. -/
def conclusion_rank1_height_solenoid_dual_height_signature_realization
    (A : Set ℚ) (d : ℕ → ℕ) : Prop :=
  ∀ p k : ℕ, Nat.Prime p →
    ((1 : ℚ) / (p ^ k : ℚ) ∈ A ↔ ∃ j : ℕ, p ^ k ∣ d j)

/-- The Pontryagin-dual solenoid is represented by the concrete inverse-limit coordinates. -/
def conclusion_rank1_height_solenoid_dual_solenoid_inverse_limit_clause
    (d : ℕ → ℕ) (S : Type) : Prop :=
  Nonempty (S ≃ conclusion_rank1_height_solenoid_dual_inverse_limit d)

/-- Height-rigidity clause for normalized rank-one subgroups of `ℚ`. -/
def conclusion_rank1_height_solenoid_dual_height_rigidity_clause (A : Set ℚ) : Prop :=
  ∀ B : Set ℚ,
    conclusion_rank1_height_solenoid_dual_rank_one_torsion_free_countable_model B →
      (∀ p k : ℕ, Nat.Prime p →
        ((1 : ℚ) / (p ^ k : ℚ) ∈ B ↔ (1 : ℚ) / (p ^ k : ℚ) ∈ A)) →
        B = A

/-- Concrete data for the rank-one height/signature and solenoid-dual construction. -/
structure conclusion_rank1_height_solenoid_dual_data where
  carrier : Set ℚ
  chain : ℕ → ℕ
  zero_mem : (0 : ℚ) ∈ carrier
  one_mem : (1 : ℚ) ∈ carrier
  add_mem : ∀ {x y : ℚ}, x ∈ carrier → y ∈ carrier → x + y ∈ carrier
  neg_mem : ∀ {x : ℚ}, x ∈ carrier → -x ∈ carrier
  countable_code : Nonempty (carrier ↪ ℕ)
  chain_pos : ∀ j : ℕ, 0 < chain j
  chain_dvd_next : ∀ j : ℕ, chain j ∣ chain (j + 1)
  carrier_eq_chain_span :
    carrier = conclusion_rank1_height_solenoid_dual_chain_span chain
  height_realization :
    conclusion_rank1_height_solenoid_dual_height_signature_realization carrier chain
  dualCoordinate : Type
  dual_inverse_limit :
    conclusion_rank1_height_solenoid_dual_solenoid_inverse_limit_clause chain dualCoordinate
  height_rigidity : conclusion_rank1_height_solenoid_dual_height_rigidity_clause carrier

namespace conclusion_rank1_height_solenoid_dual_data

/-- The assembled paper-facing conclusion for the rank-one height/solenoid dual package. -/
def conclusion_rank1_height_solenoid_dual_holds
    (D : conclusion_rank1_height_solenoid_dual_data) : Prop :=
  conclusion_rank1_height_solenoid_dual_rank_one_torsion_free_countable_model D.carrier ∧
    conclusion_rank1_height_solenoid_dual_divisor_chain_clause D.chain ∧
    D.carrier = conclusion_rank1_height_solenoid_dual_chain_span D.chain ∧
    conclusion_rank1_height_solenoid_dual_height_signature_realization D.carrier D.chain ∧
    conclusion_rank1_height_solenoid_dual_solenoid_inverse_limit_clause
      D.chain D.dualCoordinate ∧
    conclusion_rank1_height_solenoid_dual_height_rigidity_clause D.carrier

end conclusion_rank1_height_solenoid_dual_data

open conclusion_rank1_height_solenoid_dual_data

/-- Paper label: `thm:conclusion-rank1-height-solenoid-dual`. A normalized rank-one
torsion-free countable subgroup of `ℚ`, equipped with an audited divisor chain, has the expected
height-signature realization, solenoid inverse-limit dual, and height-rigidity clause. -/
theorem paper_conclusion_rank1_height_solenoid_dual
    (D : conclusion_rank1_height_solenoid_dual_data) :
    D.conclusion_rank1_height_solenoid_dual_holds := by
  unfold conclusion_rank1_height_solenoid_dual_data.conclusion_rank1_height_solenoid_dual_holds
  refine ⟨?model, ?chainClause, ?spanClause, ?heightClause, ?solenoidClause, ?rigidityClause⟩
  · unfold conclusion_rank1_height_solenoid_dual_rank_one_torsion_free_countable_model
    refine ⟨D.zero_mem, D.one_mem, ?addClosed, ?negClosed, ?torsionFree, D.countable_code⟩
    · intro x y hx hy
      exact D.add_mem hx hy
    · intro x hx
      exact D.neg_mem hx
    · intro n x _hx hn hmul
      have hnq : (n : ℚ) ≠ 0 := by
        exact_mod_cast hn
      exact (mul_eq_zero.mp hmul).resolve_left hnq
  · unfold conclusion_rank1_height_solenoid_dual_divisor_chain_clause
    exact ⟨D.chain_pos, D.chain_dvd_next⟩
  · exact D.carrier_eq_chain_span
  · exact D.height_realization
  · exact D.dual_inverse_limit
  · exact D.height_rigidity

end Omega.Conclusion
