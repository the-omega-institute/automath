import Mathlib.Tactic

namespace Omega.Zeta

/-- Weighted ledger for a finite chain state: coordinate `i` contributes weight `i`. -/
def xi_chain_idempotent_nonautonomous_finite_termination_energy {n : ℕ}
    (F : Finset (Fin n)) : ℕ :=
  ∑ i ∈ F, i.val

/-- The nonautonomous idempotent update associated to the next visible mask. -/
def xi_chain_idempotent_nonautonomous_finite_termination_update {n : ℕ}
    (F G : Finset (Fin n)) : Finset (Fin n) :=
  F ∩ G

lemma xi_chain_idempotent_nonautonomous_finite_termination_update_subset {n : ℕ}
    (F G : Finset (Fin n)) :
    xi_chain_idempotent_nonautonomous_finite_termination_update F G ⊆ F := by
  intro i hi
  exact (Finset.mem_inter.mp hi).1

lemma xi_chain_idempotent_nonautonomous_finite_termination_energy_mono {n : ℕ}
    (F G : Finset (Fin n)) :
    xi_chain_idempotent_nonautonomous_finite_termination_energy
        (xi_chain_idempotent_nonautonomous_finite_termination_update F G) ≤
      xi_chain_idempotent_nonautonomous_finite_termination_energy F := by
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (xi_chain_idempotent_nonautonomous_finite_termination_update_subset F G)
    (by intro i _ _; exact Nat.zero_le i.val)

lemma xi_chain_idempotent_nonautonomous_finite_termination_energy_strict {n : ℕ}
    (F G : Finset (Fin n))
    (hzero : ∀ i ∈ F, i.val = 0 → i ∈ G)
    (hstrict :
      xi_chain_idempotent_nonautonomous_finite_termination_update F G ⊂ F) :
    xi_chain_idempotent_nonautonomous_finite_termination_energy
        (xi_chain_idempotent_nonautonomous_finite_termination_update F G) <
      xi_chain_idempotent_nonautonomous_finite_termination_energy F := by
  classical
  have hsubset :
      xi_chain_idempotent_nonautonomous_finite_termination_update F G ⊆ F :=
    (Finset.ssubset_iff_subset_ne.mp hstrict).1
  rcases (Finset.ssubset_iff_of_subset hsubset).mp hstrict with ⟨i, hiF, hiNot⟩
  have hiNotG : i ∉ G := by
    intro hiG
    exact hiNot (Finset.mem_inter.mpr ⟨hiF, hiG⟩)
  have hi_pos : 0 < i.val := by
    exact Nat.pos_of_ne_zero (fun hival => hiNotG (hzero i hiF hival))
  exact Finset.sum_lt_sum_of_subset hsubset hiF hiNot hi_pos (by
    intro j _ _hj
    exact Nat.zero_le j.val)

lemma xi_chain_idempotent_nonautonomous_finite_termination_univ_energy (n : ℕ) :
    xi_chain_idempotent_nonautonomous_finite_termination_energy
        (Finset.univ : Finset (Fin n)) =
      n * (n - 1) / 2 := by
  rw [xi_chain_idempotent_nonautonomous_finite_termination_energy]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i) n]
  exact Finset.sum_range_id n

lemma xi_chain_idempotent_nonautonomous_finite_termination_energy_bound {n : ℕ}
    (F : Finset (Fin n)) :
    xi_chain_idempotent_nonautonomous_finite_termination_energy F ≤ n * (n - 1) / 2 := by
  calc
    xi_chain_idempotent_nonautonomous_finite_termination_energy F ≤
        xi_chain_idempotent_nonautonomous_finite_termination_energy
          (Finset.univ : Finset (Fin n)) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
        (by intro i _ _; exact Nat.zero_le i.val)
    _ = n * (n - 1) / 2 :=
      xi_chain_idempotent_nonautonomous_finite_termination_univ_energy n

/-- Concrete finite-termination package for nonautonomous idempotent chain updates. -/
def xi_chain_idempotent_nonautonomous_finite_termination_statement : Prop :=
  (∀ {n : ℕ} (F G : Finset (Fin n)),
      xi_chain_idempotent_nonautonomous_finite_termination_energy
          (xi_chain_idempotent_nonautonomous_finite_termination_update F G) ≤
        xi_chain_idempotent_nonautonomous_finite_termination_energy F) ∧
    (∀ {n : ℕ} (F G : Finset (Fin n)),
      (∀ i ∈ F, i.val = 0 → i ∈ G) →
        xi_chain_idempotent_nonautonomous_finite_termination_update F G ⊂ F →
          xi_chain_idempotent_nonautonomous_finite_termination_energy
              (xi_chain_idempotent_nonautonomous_finite_termination_update F G) <
            xi_chain_idempotent_nonautonomous_finite_termination_energy F) ∧
    (∀ {n : ℕ} (F : Finset (Fin n)),
      xi_chain_idempotent_nonautonomous_finite_termination_energy F ≤ n * (n - 1) / 2) ∧
    (∀ {n : ℕ} (F G : Finset (Fin n)),
      (∀ i ∈ F, i.val = 0 → i ∈ G) →
        xi_chain_idempotent_nonautonomous_finite_termination_update F G = F ∨
          xi_chain_idempotent_nonautonomous_finite_termination_energy
              (xi_chain_idempotent_nonautonomous_finite_termination_update F G) <
            xi_chain_idempotent_nonautonomous_finite_termination_energy F)

/-- Paper label: `thm:xi-chain-idempotent-nonautonomous-finite-termination`. -/
theorem paper_xi_chain_idempotent_nonautonomous_finite_termination :
    xi_chain_idempotent_nonautonomous_finite_termination_statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n F G
    exact xi_chain_idempotent_nonautonomous_finite_termination_energy_mono F G
  · intro n F G hzero hstrict
    exact xi_chain_idempotent_nonautonomous_finite_termination_energy_strict F G hzero hstrict
  · intro n F
    exact xi_chain_idempotent_nonautonomous_finite_termination_energy_bound F
  · intro n F G hzero
    by_cases hEq : xi_chain_idempotent_nonautonomous_finite_termination_update F G = F
    · exact Or.inl hEq
    · refine Or.inr ?_
      have hsubset :
          xi_chain_idempotent_nonautonomous_finite_termination_update F G ⊂ F :=
        Finset.ssubset_iff_subset_ne.mpr
          ⟨xi_chain_idempotent_nonautonomous_finite_termination_update_subset F G, hEq⟩
      exact xi_chain_idempotent_nonautonomous_finite_termination_energy_strict F G hzero hsubset

end Omega.Zeta
