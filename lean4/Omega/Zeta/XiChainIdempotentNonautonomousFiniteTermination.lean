import Mathlib.Tactic
import Omega.Zeta.XiChainIdempotentStarSaturationComparableGcd

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

theorem xi_chain_idempotent_nonautonomous_finite_termination_statement_verified :
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

/-- Paper label: `thm:xi-chain-idempotent-nonautonomous-finite-termination`. -/
theorem paper_xi_chain_idempotent_nonautonomous_finite_termination {n : ℕ}
    (F G : ℕ → Finset (Fin n))
    (hstep : ∀ t : ℕ, G (t + 1) = chainIdempotentProduct (F t) (G t))
    (hzeroF : ∀ t (i : Fin n), i.1 = 0 → i ∈ F t)
    (hzeroG : ∀ t (i : Fin n), i.1 = 0 → i ∈ G t) :
    ∀ T : ℕ, ((Finset.range T).filter (fun t => G (t + 1) ≠ G t)).card ≤
      ∑ i ∈ G 0, i.1 := by
  classical
  let E : ℕ → ℕ := fun t => ∑ i ∈ G t, i.1
  have hnext_subset : ∀ t : ℕ, G (t + 1) ⊆ G t := by
    intro t i hi
    have hi' : i ∈ chainIdempotentProduct (F t) (G t) := by
      simpa [hstep t] using hi
    rw [chainIdempotentProduct_eq_inter] at hi'
    exact (Finset.mem_inter.mp hi').2
  have hstrict_drop : ∀ t : ℕ, G (t + 1) ≠ G t → E (t + 1) < E t := by
    intro t hchange
    have hproper : G (t + 1) ⊂ G t := by
      exact ⟨hnext_subset t, by
        intro hsub
        exact hchange (Finset.Subset.antisymm (hnext_subset t) hsub)⟩
    obtain ⟨i, hiG, hiNext⟩ := Finset.exists_of_ssubset hproper
    have hiFnot : i ∉ F t := by
      intro hiF
      exact hiNext (by
        rw [hstep t, chainIdempotentProduct_eq_inter]
        exact Finset.mem_inter.mpr ⟨hiF, hiG⟩)
    have hival_pos : 0 < i.1 := by
      cases hival : i.1 with
      | zero =>
          have _ : i ∈ G t := hzeroG t i hival
          exact (hiFnot (hzeroF t i hival)).elim
      | succ k =>
          exact Nat.succ_pos k
    have hsum_split :
        E t = (∑ j ∈ G t \ G (t + 1), j.1) + E (t + 1) := by
      dsimp [E]
      exact (Finset.sum_sdiff (hnext_subset t)).symm
    have hremoved_pos : 0 < ∑ j ∈ G t \ G (t + 1), j.1 := by
      refine Finset.sum_pos' (fun j _ => Nat.zero_le j.1) ⟨i, ?_, hival_pos⟩
      exact Finset.mem_sdiff.mpr ⟨hiG, hiNext⟩
    rw [hsum_split]
    exact Nat.lt_add_of_pos_left hremoved_pos
  have hbound : ∀ T : ℕ,
      ((Finset.range T).filter (fun t => G (t + 1) ≠ G t)).card + E T ≤ E 0 := by
    intro T
    induction T with
    | zero =>
        simp [E]
    | succ T ih =>
        by_cases hchange : G (T + 1) ≠ G T
        · have hdrop : E (T + 1) + 1 ≤ E T := by
            exact Nat.succ_le_iff.mpr (hstrict_drop T hchange)
          have hcard :
              ((Finset.range (T + 1)).filter (fun t => G (t + 1) ≠ G t)).card =
                1 + ((Finset.range T).filter (fun t => G (t + 1) ≠ G t)).card := by
            rw [Finset.range_add_one, Finset.filter_insert, if_pos hchange]
            rw [Finset.card_insert_of_notMem]
            · omega
            · simp
          rw [hcard]
          nlinarith
        · have hsame : G (T + 1) = G T := not_not.mp hchange
          have hE : E (T + 1) = E T := by
            simp [E, hsame]
          have hcard :
              ((Finset.range (T + 1)).filter (fun t => G (t + 1) ≠ G t)).card =
                ((Finset.range T).filter (fun t => G (t + 1) ≠ G t)).card := by
            rw [Finset.range_add_one, Finset.filter_insert, if_neg hchange]
          rw [hcard, hE]
          exact ih
  intro T
  exact Nat.le_of_add_right_le (hbound T)

end Omega.Zeta
